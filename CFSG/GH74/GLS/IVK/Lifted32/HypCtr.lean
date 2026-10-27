module

public import CFSG.GH74.GLS.IVK.Lifted32.HypFAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.Stage1.Thm4.Core98

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm4 CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Local (Cen toBar barOf)
open CFSG.GH74.GLS.Stage1.Thm2.Recip (II4_44 cSec)
open scoped commutatorElement

namespace Hyp

section Aux

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem isSylowOf_map_hom {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_bar {P D : Subgroup G} (h : IsSylowOf 2 P D) (hD : D ≤ Cz z) :
    IsSylowOf 2 (barOf z P) (barOf z D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : P ≤ Cz z := h.le.trans hD
  have h' : IsSylowOf 2 (P.subgroupOf (Cz z)) (D.subgroupOf (Cz z)) := by
    refine (isSylowOf_map_subtype_iff (p := 2) (Cz z) (A := P.subgroupOf (Cz z))
      (B := D.subgroupOf (Cz z))).1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP, Subgroup.map_subgroupOf_eq_of_le hD]
    exact h
  exact isSylowOf_map_hom h' (toBar z)

theorem C1_normal (hstd : Std4 G z S K₁ K₂) {x c : G} (hx : x ∈ Cz z)
    (hc : c ∈ Cz z ⊓ normalizer (K₁ : Set G)) : x * c * x⁻¹ ∈ Cz z ⊓ normalizer (K₁ : Set G) := by
  have hperm : ∀ c ∈ Cz z, (cmap c K₁ = K₁ ∧ cmap c K₂ = K₂) ∨ (cmap c K₁ = K₂ ∧ cmap c K₂ = K₁) :=
    fun c hc => IVK.Lifted.std4_perm_cmap hstd hc
  have hfix : cmap c K₁ = K₁ ∧ cmap c K₂ = K₂ := by
    rcases hperm c hc.1 with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd (((IVK.Lifted.cmap_eq_iff_normalizer K₁ c).2 hc.2).symm.trans h1) hstd.ne
  have hxc : x * c * x⁻¹ ∈ Cz z := mul_mem (mul_mem hx hc.1) (inv_mem hx)
  refine Subgroup.mem_inf.2 ⟨hxc, (IVK.Lifted.cmap_eq_iff_normalizer K₁ _).1 ?_⟩
  have hK' : cmap x⁻¹ K₁ = K₁ ∨ cmap x⁻¹ K₁ = K₂ := by
    rcases hperm x⁻¹ (inv_mem hx) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hcK' : cmap c (cmap x⁻¹ K₁) = cmap x⁻¹ K₁ := by
    rcases hK' with h1 | h1
    · rw [h1]
      exact hfix.1
    · rw [h1]
      exact hfix.2
  calc cmap (x * c * x⁻¹) K₁ = cmap x (cmap c (cmap x⁻¹ K₁)) := by rw [cmap_cmap, cmap_cmap]
    _ = cmap x (cmap x⁻¹ K₁) := by rw [hcK']
    _ = K₁ := cmap_cancel x K₁

theorem C_le_normalizer_C1 (hstd : Std4 G z S K₁ K₂) :
    Cz z ≤ normalizer ((Cz z ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.mem_normalizer_fintype (fun _ hn => C1_normal hstd hx hn)

theorem C_le_normalizer_C2 (hstd : Std4 G z S K₁ K₂) :
    Cz z ≤ normalizer ((Cz z ⊓ normalizer (K₂ : Set G) : Subgroup G) : Set G) :=
  C_le_normalizer_C1 hstd.swap

theorem bar_inf_normalizer {X K : Subgroup G} (hKC : K ≤ Cz z)
    (hK : IsPComponent 2 (K.subgroupOf (Cz z))) :
    barOf z (X ⊓ normalizer (K : Set G)) =
      barOf z X ⊓ normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, ⟨hcX, hcN⟩, rfl⟩ := mem_barOf.1 hy
    exact ⟨toBar_mem_barOf hcX, (mem_normalizer_iff_bar hKC hK).1 hcN⟩
  · rintro ⟨hy1, hy2⟩
    obtain ⟨c, hcX, rfl⟩ := mem_barOf.1 hy1
    exact mem_barOf.2 ⟨c, ⟨hcX, (mem_normalizer_iff_bar hKC hK).2 hy2⟩, rfl⟩

theorem bar_C_inf_normalizer {K : Subgroup G} (hKC : K ≤ Cz z)
    (hK : IsPComponent 2 (K.subgroupOf (Cz z))) :
    barOf z (Cz z ⊓ normalizer (K : Set G)) =
      normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  ext y
  obtain ⟨c, rfl⟩ := toBar_surjective (z := z) y
  constructor
  · intro hy
    obtain ⟨d, ⟨-, hdN⟩, hdc⟩ := mem_barOf.1 hy
    rw [← hdc]
    exact (mem_normalizer_iff_bar hKC hK).1 hdN
  · intro hy
    exact mem_barOf.2 ⟨c, ⟨c.2, (mem_normalizer_iff_bar hKC hK).2 hy⟩, rfl⟩

theorem normalizer_le_normalizer_centralizer {X : Type*} [Group X] (H : Subgroup X) :
    normalizer (H : Set X) ≤ normalizer ((centralizer (H : Set X) : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    have h1 : g⁻¹ * h * g ∈ H := (hg (g⁻¹ * h * g)).2 (by simpa [mul_assoc] using hh)
    have h2 := hx _ h1
    calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [h2]
      _ = (g * x * g⁻¹) * h := by group
  · intro hx h hh
    have h1 : g * h * g⁻¹ ∈ H := (hg h).1 hh
    have h2 := hx _ h1
    have e1 : (g * h * g⁻¹) * (g * x * g⁻¹) = g * (h * x) * g⁻¹ := by group
    have e2 : (g * x * g⁻¹) * (g * h * g⁻¹) = g * (x * h) * g⁻¹ := by group
    rw [e1, e2] at h2
    have := mul_right_cancel h2
    exact mul_left_cancel this

theorem bar_comm' (hC : Cfg5 G z S K₁ K₂) :
    barOf z K₂ ≤ centralizer ((barOf z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.1 (bar_comm hC hh) b hb).symm

theorem mem_cSec_of_bar_centralizes {B : Subgroup G} (hBC : B ≤ Cz z)
    (hB : IsPComponent 2 (B.subgroupOf (Cz z))) {s : ↥(Cz z)}
    (hs : toBar z s ∈ centralizer ((barOf z B : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :
    (s : G) ∈ cSec B := by
  have hN : (s : G) ∈ normalizer (B : Set G) :=
    (mem_normalizer_iff_bar hBC hB).2 (Subgroup.centralizer_le_normalizer _ hs)
  refine ⟨hN, TwoThin.mem_normalizer_pPrimeCoreOf hN, fun k hk => ?_⟩
  have hkB : ⁅k, (s : G)⁆ ∈ B := by
    have h1 : (s : G) * k⁻¹ * (s : G)⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hN k⁻¹).1 (B.inv_mem hk)
    have : ⁅k, (s : G)⁆ = k * ((s : G) * k⁻¹ * (s : G)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact B.mul_mem hk h1
  have hO : ⁅k, (s : G)⁆ ∈ Oz z := by
    have hk' : toBar z ⟨k, hBC hk⟩ ∈ barOf z B := toBar_mem_barOf hk
    have h1 := Subgroup.mem_centralizer_iff.1 hs _ hk'
    have h2 : toBar z ⁅(⟨k, hBC hk⟩ : ↥(Cz z)), s⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have := (toBar_eq_one_iff).1 h2
    simpa [commutatorElement_def] using this
  have hker : (⟨⁅k, (s : G)⁆, hkB⟩ : ↥B) ∈ (phiK hBC).ker := (mem_ker_phiK hBC).2 hO
  rw [L97.phiK_ker hBC hB] at hker
  exact ⟨⟨⁅k, (s : G)⁆, hkB⟩, hker, rfl⟩

theorem sylow_P_aux (hC : Cfg5 G z S K₁ K₂) (h52 : L52 S K₁ K₂) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) :
    IsSylowOf 2 (barOf z S ⊓ barOf z A)
      (centralizer ((barOf z B : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBc : B = K₁ ∨ B = K₂ := by
    rcases hAB with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hAc : A = K₁ ∨ A = K₂ := by
    rcases hAB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hBC := K_le_Cz hC hBc
  have hAC := K_le_Cz hC hAc
  have hBp := pcomp_of hC hBc
  have hSC : S ≤ Cz z := hC.std.sylow.le
  have hCnorm : Cz z ≤ normalizer ((Cz z ⊓ normalizer (B : Set G) : Subgroup G) : Set G) := by
    rcases hBc with rfl | rfl
    · exact C_le_normalizer_C1 hC.std
    · exact C_le_normalizer_C2 hC.std
  have hSyl1 : IsSylowOf 2 (S ⊓ (Cz z ⊓ normalizer (B : Set G))) (Cz z ⊓ normalizer (B : Set G)) :=
    hC.std.sylow.inf_of_le_normalizer inf_le_left hCnorm
  have hbar := isSylowOf_bar hSyl1 inf_le_left
  have e1 : S ⊓ (Cz z ⊓ normalizer (B : Set G)) = S ⊓ normalizer (B : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hSC]
  rw [e1, bar_inf_normalizer hBC hBp, bar_C_inf_normalizer hBC hBp] at hbar
  have hCN : centralizer ((barOf z B : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ≤
      normalizer ((barOf z B : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
    Subgroup.centralizer_le_normalizer _
  have h2 := hbar.inf_of_le_normalizer hCN (normalizer_le_normalizer_centralizer _)
  rw [inf_assoc, inf_eq_right.2 hCN] at h2
  have e2 : barOf z S ⊓ centralizer ((barOf z B : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) =
      barOf z S ⊓ barOf z A := by
    apply le_antisymm
    · rintro y ⟨hyS, hyC⟩
      obtain ⟨c, hcS, rfl⟩ := mem_barOf.1 hyS
      have hcs := mem_cSec_of_bar_centralizes hBC hBp hyC
      have hcQ : (c : G) ∈ Qof S B := ⟨hcS, hcs⟩
      have hcP : (c : G) ∈ Pof S A := by
        rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [← h52.2]; exact hcQ
        · rw [← h52.1]; exact hcQ
      exact ⟨hyS, toBar_mem_barOf hcP.2⟩
    · rintro y ⟨hyS, hyA⟩
      refine ⟨hyS, ?_⟩
      rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact bar_comm hC hyA
      · exact bar_comm' hC hyA
  rwa [e2] at h2

theorem sylow_S_bar (hC : Cfg5 G z S K₁ K₂) : IsSylowOf 2 (barOf z S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h' : IsSylowOf 2 (S.subgroupOf (Cz z)) ⊤ := by
    refine (isSylowOf_map_subtype_iff (p := 2) (Cz z) (A := S.subgroupOf (Cz z)) (B := ⊤)).1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hC.std.sylow.le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hC.std.sylow
  exact sylow_map_mk (N := pPrimeCore 2 ↥(Cz z)) h'

omit [Finite G] in
theorem toBar_mem_commutator {a : G} (ha : a ∈ commBar z) (haC : a ∈ Cz z) :
    toBar z ⟨a, haC⟩ ∈ commutator (CentralizerBar z) := by
  let M : Subgroup G := ((commutator (CentralizerBar z)).comap (toBar z)).map (Cz z).subtype
  have h1 : ⁅Cz z, Cz z⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, hg₁⟩ : ↥(Cz z)), ⟨g₂, hg₂⟩⁆, ?_, rfl⟩
    show toBar z ⁅(⟨g₁, hg₁⟩ : ↥(Cz z)), ⟨g₂, hg₂⟩⁆ ∈ commutator (CentralizerBar z)
    rw [commutatorElement_def, map_mul, map_mul, map_inv, map_inv]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 : Oz z ≤ M := by
    intro o ho
    have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
    refine ⟨⟨o, hoC⟩, ?_, rfl⟩
    show toBar z ⟨o, hoC⟩ ∈ commutator (CentralizerBar z)
    rw [(toBar_eq_one_iff (c := ⟨o, hoC⟩)).2 ho]
    exact one_mem _
  obtain ⟨c, hc, hca⟩ := sup_le h1 h2 ha
  have : c = ⟨a, haC⟩ := Subtype.ext hca
  rw [← this]
  exact hc

theorem toBar_ne_zBar (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) {a : G} (haC : a ∈ Cz z)
    (haS : a ∈ S) (ha : a ∉ zpowers z) : toBar z ⟨a, haC⟩ ≠ zBar z := by
  intro h
  have h1 : (⟨a, haC⟩ : ↥(Cz z))⁻¹ * zElt z ∈ pPrimeCore 2 ↥(Cz z) := QuotientGroup.eq.1 h
  have h2 : a⁻¹ * z ∈ Oz z := (mem_Oz_iff (c := (⟨a, haC⟩ : ↥(Cz z))⁻¹ * zElt z)).2 h1
  have hzS : z ∈ S := (m4_of_std hII hC.std).z_mem_S
  have h3 : a⁻¹ * z ∈ S ⊓ Oz z := ⟨S.mul_mem (S.inv_mem haS) hzS, h2⟩
  rw [S_inf_Oz hC, Subgroup.mem_bot] at h3
  apply ha
  have : a = z := by
    have := congrArg (fun w => a * w) h3
    simpa using this.symm
  rw [this]
  exact mem_zpowers z

theorem extr_bar (hC : Cfg5 G z S K₁ K₂) {a : G} (haC : a ∈ Cz z) (haS : a ∈ S)
    (ha2 : orderOf a = 2)
    (hE : IsSylowOf 2 (Wof S a) (Cz z ⊓ centralizer ({a} : Set G))) :
    IsSylowOf 2
      (IVK.Prod3.T1 (barOf z S) (barOf z K₁) ⊓
        centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)))
      (centralizer ({toBar z ⟨a, haC⟩} : Set (CentralizerBar z)) ⊓
        (barOf z K₁ ⊔ barOf z K₂ ⊔ IVK.Prod3.T1 (barOf z S) (barOf z K₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  set t : ↥(Cz z) := ⟨a, haC⟩ with ht
  have htt : t * t = 1 := Subtype.ext haa
  have hK1C := K_le_Cz hC (Or.inl rfl)
  have hK1p := pcomp_of hC (Or.inl rfl)
  let C₁ : Subgroup G := Cz z ⊓ normalizer (K₁ : Set G)
  let D : Subgroup G := C₁ ⊓ centralizer ({a} : Set G)
  have hDE : D ≤ Cz z ⊓ centralizer ({a} : Set G) := inf_le_inf_right _ inf_le_left
  have hEnorm : Cz z ⊓ centralizer ({a} : Set G) ≤ normalizer (D : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype (fun d hd => ⟨C1_normal hC.std he.1 hd.1, ?_⟩)
    have hea : Commute e a := Subgroup.mem_centralizer_singleton_iff.1 he.2
    have hda : Commute d a := Subgroup.mem_centralizer_singleton_iff.1 hd.2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hea.mul_left hda).mul_left hea.inv_left)
  have hSylD : IsSylowOf 2 (Wof S a ⊓ D) D := hE.inf_of_le_normalizer hDE hEnorm
  have hDC : D ≤ Cz z := inf_le_left.trans inf_le_left
  have hbar := isSylowOf_bar hSylD hDC
  have eY : barOf z D = centralizer ({toBar z t} : Set (CentralizerBar z)) ⊓
      normalizer ((barOf z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
    ext y
    obtain ⟨c, rfl⟩ := toBar_surjective (z := z) y
    constructor
    · intro hy
      obtain ⟨d, ⟨⟨hdC, hdN⟩, hdcent⟩, hdc⟩ := mem_barOf.1 hy
      refine ⟨?_, ?_⟩
      · rw [← hdc]
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hdcent)
      · rw [← hdc]
        exact (mem_normalizer_iff_bar hK1C hK1p).1 hdN
    · rintro ⟨hc1, hc2⟩
      have hmap := CFSG.ComponentClassification.UnbalancedLayer.map_centralizer_eq
        (R := pPrimeCore 2 ↥(Cz z)) odd_card_pPrimeCore htt
      have hc1' : toBar z c ∈ (centralizer ({t} : Set ↥(Cz z))).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(Cz z))) := by
        rw [hmap]
        exact hc1
      obtain ⟨d, hd, hdc⟩ := hc1'
      have hdc' : toBar z d = toBar z c := hdc
      have hdN : (d : G) ∈ normalizer (K₁ : Set G) := by
        rw [mem_normalizer_iff_bar hK1C hK1p, hdc']
        exact hc2
      have hdcent : (d : G) ∈ centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.1 hd
        exact congrArg Subtype.val this
      exact mem_barOf.2 ⟨d, ⟨⟨d.2, hdN⟩, hdcent⟩, hdc'⟩
  have eX : barOf z (Wof S a ⊓ D) =
      (barOf z S ⊓ normalizer ((barOf z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) ⊓
        centralizer ({toBar z t} : Set (CentralizerBar z)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, ⟨⟨hcS, hcca⟩, ⟨⟨hcC, hcN⟩, hcca'⟩⟩, rfl⟩ := mem_barOf.1 hy
      refine ⟨⟨toBar_mem_barOf hcS, (mem_normalizer_iff_bar hK1C hK1p).1 hcN⟩, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hcca)
    · rintro ⟨⟨hyS, hyN⟩, hyC⟩
      obtain ⟨c, hcS, rfl⟩ := mem_barOf.1 hyS
      have hcN : (c : G) ∈ normalizer (K₁ : Set G) := (mem_normalizer_iff_bar hK1C hK1p).2 hyN
      have hca : (c : G) * a = a * (c : G) := by
        have hcomm : toBar z c * toBar z t = toBar z t * toBar z c :=
          Subgroup.mem_centralizer_singleton_iff.1 hyC
        have hwS : ⁅(c : G), a⁆ ∈ S := by
          simp only [commutatorElement_def]
          exact S.mul_mem (S.mul_mem (S.mul_mem hcS haS) (S.inv_mem hcS)) (S.inv_mem haS)
        have hwO : ⁅(c : G), a⁆ ∈ Oz z := by
          have h2 : toBar z ⁅c, t⁆ = 1 := by
            rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
            group
          have := (toBar_eq_one_iff).1 h2
          simpa [commutatorElement_def, ht] using this
        have hw : ⁅(c : G), a⁆ ∈ S ⊓ Oz z := ⟨hwS, hwO⟩
        rw [S_inf_Oz hC, Subgroup.mem_bot] at hw
        exact commutatorElement_eq_one_iff_mul_comm.1 hw
      exact mem_barOf.2 ⟨c, ⟨⟨hcS, Subgroup.mem_centralizer_singleton_iff.2 hca⟩,
        ⟨⟨c.2, hcN⟩, Subgroup.mem_centralizer_singleton_iff.2 hca⟩⟩, rfl⟩
  rw [eX, eY] at hbar
  refine hbar.of_le ?_ ?_
  · intro y hy
    exact ⟨hy.2, Subgroup.mem_sup_right hy.1⟩
  · intro y hy
    refine ⟨hy.1, ?_⟩
    have hle : barOf z K₁ ⊔ barOf z K₂ ⊔ IVK.Prod3.T1 (barOf z S) (barOf z K₁) ≤
        normalizer ((barOf z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
      sup_le (sup_le Subgroup.le_normalizer ((bar_comm' hC).trans (Subgroup.centralizer_le_normalizer _)))
        inf_le_right
    exact hle hy.2

end Aux

end Hyp

open Hyp

section Deliverables

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem sylow_P_of_L52 (_hII : II4_4_4_center) (hctr : Ctr5 G z S K₁ K₂ a x) (h52 : L52 S K₁ K₂) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S ⊓ barOf z K₁)
        (centralizer ((barOf z K₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 (barOf z S ⊓ barOf z K₂)
        (centralizer ((barOf z K₁ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z))) :=
  ⟨sylow_P_aux hctr.cfg h52 (Or.inl ⟨rfl, rfl⟩), sylow_P_aux hctr.cfg h52 (Or.inr ⟨rfl, rfl⟩)⟩

theorem hyp_of_ctr5 (hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hctr : Ctr5 G z S K₁ K₂ a x) (haC : a ∈ Cen z) :
    IVK.Prod3.Hyp (CentralizerBar z) (barOf z K₁) (barOf z K₂) (zBar z) (barOf z S)
      (toBar z ⟨a, haC⟩) where
  setting := setting_of_cfg5 hII h44 hctr.cfg
  sylow := sylow_S_bar hctr.cfg
  a_mem := ⟨toBar_mem_barOf (c := ⟨a, haC⟩) hctr.elt.mem,
    (mem_normalizer_iff_bar (K_le_Cz hctr.cfg (Or.inl rfl)) (pcomp_of hctr.cfg (Or.inl rfl))
      (c := ⟨a, haC⟩)).1 hctr.elt.f₁.1⟩
  a_ord := CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two
    (R := pPrimeCore 2 ↥(Cz z)) odd_card_pPrimeCore
    ((Subgroup.orderOf_coe (⟨a, haC⟩ : ↥(Cz z))).symm.trans hctr.elt.inv)
  f₁ := inducesFAut_bar hII h44 h2A7 hctr.cfg (Or.inl rfl) haC hctr.elt.inv hctr.elt.f₁
  f₂ := inducesFAut_bar hII h44 h2A7 hctr.cfg (Or.inr rfl) haC hctr.elt.inv hctr.elt.f₂
  a_comm := toBar_mem_commutator hctr.comm haC
  a_ne_z := toBar_ne_zBar hII hctr.cfg haC hctr.elt.mem hctr.elt.ne
  extr := extr_bar hctr.cfg haC hctr.elt.mem hctr.elt.inv hctr.extr

end Deliverables

end CFSG.GH74.GLS.IVK.Lifted32
