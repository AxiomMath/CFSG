module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Fourteen
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NineAlt
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NineHol
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Eight

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUp
open scoped commutatorElement

theorem eq_one_of_pow_two_pow_of_pow_three {Γ : Type*} [Group Γ] {y : Γ} {k : ℕ}
    (h2 : y ^ (2 ^ k) = 1) (h3 : y ^ 3 = 1) : y = 1 := by
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hord : orderOf y ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [hcop] at hord
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)

section Block

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.exists_altBlock_of_lift (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1)
    {H B : Subgroup (MulAut V)} (hHG : H ≤ G) (hlift : Lift5 H Y B) (hperf : ⁅B, B⁆ = B) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ D : AltBlock B n, ∀ b : ↥B, D.θ b = 1 → b = 1 := by
  obtain ⟨hYB, hBH, hsubB, hc, harr⟩ := hlift
  have h3 := cfg.adm.h3
  have hperfB : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have hBY : B ≠ Y := by
    intro h
    subst h
    have : IsPGroup 3 ↥B := IsPGroup.of_card (n := 1) (by simpa using h3)
    have hs := subsingleton_of_perfect_of_isPGroup hperfB this
    have : Nat.card ↥B = 1 := Nat.card_unique
    omega
  rcases harr with heq | ⟨a, b', φ, F, -, hnat', -, -, -, -⟩
  · exact absurd (yuHol_inj heq).symm hBY
  have hnat : IsNaturalAltModule ↥(yuHol B) a := isNaturalAltModule_iff.mpr ⟨φ, hnat'⟩
  have hn2 : 2 ≤ a := by
    by_contra hlt
    push Not at hlt
    have hcomm : IsMulCommutative (alternatingGroup (Fin (2 * a + 1))) := by
      apply alternatingGroup.isMulCommutative_of_card_le_three
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have hθ1 : ∀ g : ↥B, yuTheta B φ g = 1 :=
      mult_trivial_of_perfect (yuTheta B φ) (fun g h => map_mul (yuTheta B φ) g h)
    have hcen := yuTheta_ker_le_center B φ hV hc.1
    have hBcomm : ∀ g h : ↥B, g * h = h * g := fun g h =>
      (Subgroup.mem_center_iff.mp (hcen (MonoidHom.mem_ker.mpr (hθ1 g))) h).symm
    have : IsMulCommutative ↥B := ⟨⟨hBcomm⟩⟩
    have hB1 : ∀ g : ↥B, g = 1 :=
      mult_trivial_of_perfect (M := ↥B) (fun g => g) (fun g h => rfl)
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hno
      push Not at hno
      have : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
      rw [this] at h3
      simp at h3
    exact hy1 (congrArg Subtype.val (hB1 ⟨y, hYB hy⟩))
  obtain ⟨D⟩ := exists_altBlock hV hperf hc.1 hn2 hnat
  refine ⟨a, hn2, D, fun b hb => ?_⟩
  by_contra hb1
  have hY3 : ∀ y ∈ Y, y ^ 3 = 1 := fun y hy => (cfg.sec5 hV).pow_three hy
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
    rw [this] at h3
    simp at h3
  set R : Subgroup (MulAut V) := D.θ.ker.map B.subtype with hR
  have hRne : R ≠ ⊥ := by
    intro h
    have hker : D.θ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : (g : MulAut V) ∈ R := ⟨g, hg, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (Subtype.ext this)
    exact hb1 (Subgroup.mem_bot.mp (hker ▸ (MonoidHom.mem_ker.mpr hb)))
  have hker2 : IsPGroup 2 ↥D.θ.ker := fun g => by
    obtain ⟨k, hk⟩ := D.ker_two g.1 (MonoidHom.mem_ker.mp g.2)
    exact ⟨k, Subtype.ext hk⟩
  have hR2 : IsPGroup 2 ↥R := hker2.map B.subtype
  obtain ⟨z, hzR, hz1, hz2, -⟩ := exists_central_involution hRne hR2
  obtain ⟨z₀, hz₀, rfl⟩ := hzR
  have hzcen : z₀ ∈ Subgroup.center ↥B := D.ker_central z₀ (MonoidHom.mem_ker.mp hz₀)
  have hzB : ∀ b' ∈ B, b' * (z₀ : MulAut V) = (z₀ : MulAut V) * b' := fun b' hb' =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcen ⟨b', hb'⟩)
  have hzG : (z₀ : MulAut V) ∈ G := hHG (hBH z₀.2)
  have hzC : (z₀ : MulAut V) ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) :=
    ⟨hzG, Subgroup.mem_centralizer_iff.mpr fun y hy => hzB y (hYB hy)⟩
  have hcent := cfg.cent _ hzC hz1 hz2
  have hBle : B ≤ G ⊓ Subgroup.centralizer ({(z₀ : MulAut V)} : Set (MulAut V)) := by
    intro b' hb'
    refine ⟨hHG (hBH hb'), Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hzB b' hb').symm
  have hsubB' : (Y.subgroupOf B).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hBle hcent
  let θ' : ↥B →* alternatingGroup (Fin (2 * a + 1)) := D.θ.codRestrict _ D.θ_alt
  have hθ's : Function.Surjective θ' := fun s => by
    obtain ⟨b'', hb''⟩ := D.θ_surj s.1 s.2
    exact ⟨b'', Subtype.ext hb''⟩
  have hmapsub := hsubB'.map hθ's
  have hcardA : 5 ≤ Nat.card (Fin (2 * a + 1)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hsimple : IsSimpleGroup (alternatingGroup (Fin (2 * a + 1))) :=
    alternatingGroup.isSimpleGroup hcardA
  rcases hmapsub.eq_bot_or_top_of_isSimpleGroup hsimple with hbot | htop
  · have hmem : θ' ⟨y, hYB hy⟩ ∈ (Y.subgroupOf B).map θ' := ⟨⟨y, hYB hy⟩, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : D.θ ⟨y, hYB hy⟩ = 1 := congrArg Subtype.val hmem
    obtain ⟨k, hk⟩ := D.ker_two _ h1
    have hk' : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    exact hy1 (eq_one_of_pow_two_pow_of_pow_three hk' (hY3 y hy))
  · have hle : Nat.card ↥((Y.subgroupOf B).map θ') ≤ Nat.card ↥(Y.subgroupOf B) :=
      Nat.card_le_card_of_surjective _ (θ'.subgroupMap_surjective _)
    rw [htop, Subgroup.card_top] at hle
    have hYcard : Nat.card ↥(Y.subgroupOf B) = 3 := by
      rw [← h3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    have hA60 : 60 ≤ Nat.card (alternatingGroup (Fin (2 * a + 1))) := by
      have : Nontrivial (Fin (2 * a + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h2 := nat_card_alternatingGroup (α := Fin (2 * a + 1))
      have h5 : Nat.factorial 5 ≤ Nat.factorial (Nat.card (Fin (2 * a + 1))) :=
        Nat.factorial_le hcardA
      have h6 : Nat.factorial 5 = 120 := rfl
      omega
    omega

omit [Finite V] in
theorem le_normalizer_triple {X Y : Subgroup (MulAut V)} {t : MulAut V}
    (hYt : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) :
    X ⊔ Y ⊔ Subgroup.zpowers t ≤
      Subgroup.normalizer ((X ⊔ CGT6E.conjSub t X ⊔ Y : Subgroup (MulAut V)) : Set (MulAut V)) := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hXtX : (CGT6E.conjSub t X).map (MulAut.conj t).toMonoidHom = X := by
    have : CGT6E.conjSub t (CGT6E.conjSub t X) = X := by
      rw [conjSub_conjSub, htt, conjSub_one]
    exact this
  have hYmap : Y.map (MulAut.conj t).toMonoidHom = Y := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : t * y * t⁻¹ = y := by rw [hYt y hy]; group
      simpa [MulAut.conj_apply, this] using hy
    · intro hz
      refine ⟨z, hz, ?_⟩
      have : t * z * t⁻¹ = z := by rw [hYt z hz]; group
      simpa [MulAut.conj_apply] using this
  set M₀ : Subgroup (MulAut V) := X ⊔ CGT6E.conjSub t X ⊔ Y with hM₀
  have hmap : M₀.map (MulAut.conj t).toMonoidHom ≤ M₀ := by
    rw [hM₀, Subgroup.map_sup, Subgroup.map_sup, hXtX, hYmap]
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact (le_sup_right : CGT6E.conjSub t X ≤ X ⊔ CGT6E.conjSub t X).trans le_sup_left
    · exact (le_sup_left : X ≤ X ⊔ CGT6E.conjSub t X).trans le_sup_left
  have key : ∀ h ∈ M₀, t * h * t⁻¹ ∈ M₀ := fun h hh => by
    have := hmap ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using this
  have htN : t ∈ Subgroup.normalizer (M₀ : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key h, fun hh => ?_⟩
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      calc t * (t * h * t⁻¹) * t⁻¹ = (t * t) * h * (t * t)⁻¹ := by group
        _ = h := by rw [htt]; group
    have := key _ hh
    rwa [e] at this
  have hXM : X ≤ M₀ := (le_sup_left : X ≤ X ⊔ CGT6E.conjSub t X).trans le_sup_left
  refine sup_le (sup_le (hXM.trans Subgroup.le_normalizer) (le_sup_right.trans
    Subgroup.le_normalizer)) ?_
  exact Subgroup.zpowers_le.mpr htN

theorem card_commV_triple_le {X Z Y : Subgroup (MulAut V)} (hX : Nat.card ↥(commV X) = 4)
    (hZ : Nat.card ↥(commV Z) = 4) (hY : Nat.card ↥(commV Y) = 4) :
    Nat.card ↥(commV (X ⊔ Z ⊔ Y)) ≤ 64 := by
  have h1 : commV (X ⊔ Z ⊔ Y) ≤ commV (X ⊔ Z) ⊔ commV Y := commV_sup_le _ _
  have h2 : commV (X ⊔ Z) ≤ commV X ⊔ commV Z := commV_sup_le _ _
  have c1 := card_sup_le_mul (commV X) (commV Z)
  have c2 := card_sup_le_mul (commV X ⊔ commV Z) (commV Y)
  rw [hX, hZ] at c1
  rw [hY] at c2
  calc Nat.card ↥(commV (X ⊔ Z ⊔ Y)) ≤ Nat.card ↥(commV (X ⊔ Z) ⊔ commV Y) :=
        Subgroup.card_le_of_le h1
    _ ≤ Nat.card ↥(commV X ⊔ commV Z ⊔ commV Y) :=
        Subgroup.card_le_of_le (sup_le_sup_right h2 _)
    _ ≤ Nat.card ↥(commV X ⊔ commV Z) * 4 := c2
    _ ≤ 4 * 4 * 4 := Nat.mul_le_mul_right 4 c1
    _ = 64 := by norm_num

theorem Emb5Cfg.normalizes_of_lift (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t g : MulAut V}
    (htY : ∀ y ∈ Y, t * y = y * t) (ht2 : t ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hlift : Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B) {n : ℕ} (hn : 2 ≤ n)
    (D : AltBlock B n) {x : MulAut V} (hx : x ∈ CGT6E.conjSub g Y) :
    x ∈ Subgroup.normalizer (B : Set (MulAut V)) := by
  set X : Subgroup (MulAut V) := CGT6E.conjSub g Y with hX
  set Xt : Subgroup (MulAut V) := CGT6E.conjSub t X with hXt
  set H : Subgroup (MulAut V) := X ⊔ Y ⊔ Subgroup.zpowers t with hH
  set M₀ : Subgroup (MulAut V) := X ⊔ Xt ⊔ Y with hM₀
  have hlift' := hlift
  obtain ⟨hYB, hBH, hsubB, hc, -⟩ := hlift'
  have hxH : x ∈ H := Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  have hxM : x ∈ M₀ := Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)
  by_contra hxN
  have hne : CGT6E.conjSub x B ≠ B := fun h => hxN (mem_normalizer_of_conjSub_eq h)
  obtain ⟨hA, hB'⟩ := trivial_of_conj_ne hV hBH hsubB hc hxH hne
  have hBM : B ≤ M₀ := by
    have hcc : conjClosure Y B = B := Lift5.conjClosure_eq cfg.not_isPGroup_Y hlift
    rw [← hcc]
    refine le_trans (conjClosure_mono hBH) ?_
    rw [conjClosure, Subgroup.closure_le]
    rintro _ ⟨g', hg', y, hy, rfl⟩
    have hyM : y ∈ M₀ := Subgroup.mem_sup_right hy
    have hn' := le_normalizer_triple (X := X) htY ht2 hg'
    have := (Subgroup.mem_normalizer_iff.mp hn' y).mp hyM
    exact this
  have hB'M : CGT6E.conjSub x B ≤ M₀ := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact M₀.mul_mem (M₀.mul_mem hxM (hBM hb)) (M₀.inv_mem hxM)
  have hle : commV B ⊔ commV (CGT6E.conjSub x B) ≤ commV M₀ :=
    sup_le (commV_mono hBM) (commV_mono hB'M)
  have hY4 := cfg.adm.h4
  have hX4 : Nat.card ↥(commV X) = 4 := by rw [hX, CGT6E.card_commV_conjSub]; exact hY4
  have hXt4 : Nat.card ↥(commV Xt) = 4 := by
    rw [hXt]; exact (CGT6E.card_commV_conjSub t X).trans hX4
  have hM64 : Nat.card ↥(commV M₀) ≤ 64 := card_commV_triple_le hX4 hXt4 hY4
  have hE : Nat.card ↥(commV B) = 2 ^ (2 * n) := D.card_commV
  have hE' : Nat.card ↥(commV (CGT6E.conjSub x B)) = Nat.card ↥(commV B) :=
    CGT6E.card_commV_conjSub x B
  have hdisj : commV B ⊓ commV (CGT6E.conjSub x B) = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨huE, huE'⟩
    rw [Subgroup.mem_bot]
    have hfix : ∀ b : ↥B, (b : MulAut V) u = u := fun b => hB' b b.2 u huE'
    have hmem : D.β ⟨u, huE⟩ ∈ fixV ((alternatingGroup (Fin (2 * n + 1))).map
        (coreAct (2 * n + 1))) := by
      rw [mem_fixV_map_iff]
      intro σ hσ i
      obtain ⟨b, rfl⟩ := D.θ_surj σ hσ
      have heq : coreAct (2 * n + 1) (D.θ b) (D.β ⟨u, huE⟩) = D.β ⟨u, huE⟩ := by
        rw [← D.equivar b ⟨u, huE⟩]
        congr 1
        exact Subtype.ext (hfix b)
      have := congrArg (fun w => vcoord w ((D.θ b) i)) heq
      simpa [vcoord_coreAct] using this.symm
    rw [fixV_alt_map (odd_two_mul_add_one n) (by omega)] at hmem
    have h1 : D.β ⟨u, huE⟩ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : (⟨u, huE⟩ : ↥(commV B)) = 1 := D.β.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hcard := card_sup_mul_card_inf (commV B) (commV (CGT6E.conjSub x B))
  rw [hdisj, Subgroup.card_bot, mul_one, hE', hE] at hcard
  have h16 : 16 ≤ 2 ^ (2 * n) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcardle := Subgroup.card_le_of_le hle
  rw [hcard] at hcardle
  have := Nat.mul_le_mul h16 h16
  omega

omit [Finite V] in
theorem zpowers_subgroupOf_eq {Γ : Type*} [Group Γ] {B : Subgroup Γ} {x : Γ} (hx : x ∈ B) :
    (Subgroup.zpowers x).subgroupOf B = Subgroup.zpowers (⟨x, hx⟩ : ↥B) := by
  ext z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩

omit [Finite V] in
theorem isZ3E9A4A5_of_subgroup_hom {Γ : Type} [Group Γ] {α : Type} [Fintype α] [DecidableEq α]
    {B X Y' : Subgroup Γ} (hXB : X ≤ B) (hYB : Y' ≤ B) (f : ↥B →* Equiv.Perm α)
    (hf : Function.Injective f) {c₁ c₂ : Equiv.Perm α} (h₁ : c₁.IsThreeCycle)
    (h₂ : c₂.IsThreeCycle) (hX : (X.subgroupOf B).map f = Subgroup.zpowers c₁)
    (hY : (Y'.subgroupOf B).map f = Subgroup.zpowers c₂) : IsZ3E9A4A5 ↥(X ⊔ Y') := by
  have h := isZ3E9A4A5_of_injective_threeCycles f hf h₁ h₂ hX hY
  have hsup : (X ⊔ Y').subgroupOf B = X.subgroupOf B ⊔ Y'.subgroupOf B :=
    Subgroup.subgroupOf_sup hXB hYB
  rw [← hsup] at h
  exact IsZ3E9A4A5.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (sup_le hXB hYB)) h

theorem Emb5Cfg.five_nine (cfg : Emb5Cfg G T Y) (hV : ∀ v : V, v ^ 2 = 1) {t g : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hg : g ∈ G) (hH : CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t ≠ G) :
    IsZ3E9A4A5 ↥(CGT6E.conjSub g Y ⊔ Y) ∧
      ((∀ a ∈ CGT6E.conjSub g Y, ∀ b ∈ Y, a * b = b * a) ∨
        ∃ B : Subgroup (MulAut V), ⁅B, B⁆ = B ∧
          Lift5 (CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t) Y B) := by
  set X : Subgroup (MulAut V) := CGT6E.conjSub g Y with hX
  set H : Subgroup (MulAut V) := X ⊔ Y ⊔ Subgroup.zpowers t with hHdef
  have hYG : Y ≤ G := fun y hy => (cfg.adm.hYC hy).1
  have hXG : X ≤ G := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact G.mul_mem (G.mul_mem hg (hYG hy)) (G.inv_mem hg)
  have htG : t ∈ G := ht.1
  have hHG : H ≤ G := sup_le (sup_le hXG hYG) (Subgroup.zpowers_le.mpr htG)
  have hlt : H < G := lt_of_le_of_ne hHG hH
  have htY : ∀ y ∈ Y, t * y = y * t := fun y hy => (Subgroup.mem_centralizer_iff.mp ht.2 y hy).symm
  have hcent := cfg.cent t ht ht1 ht2
  have hXH : X ≤ H := le_sup_left.trans le_sup_left
  have hYH : Y ≤ H := (le_sup_right : Y ≤ X ⊔ Y).trans le_sup_left
  have htH : Subgroup.zpowers t ≤ H := le_sup_right
  have hadm : Adm5 H (Subgroup.zpowers t) Y :=
    { hTG := htH
      hT1 := zpowers_ne_bot ht1
      hT2 := isPGroup_zpowers_of_sq ht2
      hYC := by
        refine fun y hy => ⟨hYH hy, ?_⟩
        rw [centralizer_zpowers_eq]
        exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact htY y hy
      hsub := by
        rw [centralizer_zpowers_eq]
        exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ hHG) hcent
      h3 := cfg.adm.h3
      h4 := cfg.adm.h4 }
  obtain ⟨X₁, hX₁⟩ := cfg.lift_sub hV hlt hadm
  have h3 := cfg.adm.h3
  have hX3 : Nat.card ↥X = 3 := (CGT6E.card_conjSub g Y).trans h3
  have hX4 : Nat.card ↥(commV X) = 4 := by
    rw [hX, CGT6E.card_commV_conjSub]; exact cfg.adm.h4
  by_cases hperf : ⁅X₁, X₁⁆ = X₁
  swap
  ·
    have hHN : H ≤ Subgroup.normalizer (oTwoIn H : Set (MulAut V)) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn H)
    have hO : ⁅oTwoIn Y, Y⁆ = ⊥ := by
      rw [oTwoIn_eq_bot_of_card_three h3]
      exact Subgroup.commutator_bot_left Y
    have hQY : ⁅oTwoIn H, Y⁆ = ⊥ :=
      commutator_eq_bot_of_centralizer (G₀ := H) (T := Subgroup.zpowers t) (Y := Y)
        (Q := oTwoIn H) (noTwoQuotient_of_card_three h3) (Or.inr h3) hO hadm.hT2
        (SixThree.isPGroup_oTwoIn H) (oTwoIn_le H) (htH.trans hHN) (hYH.trans hHN) hadm.hYC
        hadm.hsub
    have hsubY := Lift5.subnormal_of_not_perfect hV h3 hX₁ hperf hQY
    have hp3Y : IsPGroup 3 ↥(Y.subgroupOf H) :=
      (IsPGroup.of_card (n := 1) (by simpa using h3) : IsPGroup 3 ↥Y).of_equiv
        (Subgroup.subgroupOfEquivOfLe hYH).symm
    have hp3X : IsPGroup 3 ↥(X.subgroupOf H) :=
      (IsPGroup.of_card (n := 1) (by simpa using hX3) : IsPGroup 3 ↥X).of_equiv
        (Subgroup.subgroupOfEquivOfLe hXH).symm
    have hle : Y.subgroupOf H ≤ pCore 3 ↥H := le_pCore_of_isSubnormal hsubY hp3Y
    have hsup : IsPGroup 3 ↥(X.subgroupOf H ⊔ pCore 3 ↥H) :=
      IsPGroup.to_sup_of_normal_right hp3X pCore_isPGroup
    have hsup' : (X ⊔ Y).subgroupOf H = X.subgroupOf H ⊔ Y.subgroupOf H :=
      Subgroup.subgroupOf_sup hXH hYH
    have hJle : (X ⊔ Y).subgroupOf H ≤ X.subgroupOf H ⊔ pCore 3 ↥H := by
      rw [hsup']; exact sup_le_sup_left hle _
    have hJ3 : IsPGroup 3 ↥(X ⊔ Y) :=
      (hsup.to_le hJle).of_equiv (Subgroup.subgroupOfEquivOfLe (sup_le hXH hYH))
    have hcomm := commute_of_sup_three_group hV hX4.le cfg.adm.h4.le hJ3
    refine ⟨isZ3E9A4A5_of_commute hX3 h3 fun a ha b hb =>
      hcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb), Or.inl fun a ha b hb =>
      hcomm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)⟩
  ·
    obtain ⟨n, hn, D, hR⟩ := cfg.exists_altBlock_of_lift hV hHG hX₁ hperf
    have hY3 : ∀ y ∈ Y, y ^ 3 = 1 := fun y hy => (cfg.sec5 hV).pow_three hy
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hno
      push Not at hno
      have : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).mpr hno
      rw [this] at h3
      simp at h3
    have hYz : Subgroup.zpowers y = Y := CGT6E.zpowers_eq_of_card_three h3 hy hy1
    set x : MulAut V := g * y * g⁻¹ with hxdef
    have hxX : x ∈ X := CGT6E.conj_mem_conjSub hy
    have hx1 : x ≠ 1 := by
      intro h
      apply hy1
      have : g * y * g⁻¹ = 1 := h
      simpa using this
    have hXz : Subgroup.zpowers x = X := CGT6E.zpowers_eq_of_card_three hX3 hxX hx1
    have hx3 : x ^ 3 = 1 := by
      have : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hxX⟩)
        rwa [hX3] at this
      simpa using congrArg Subtype.val this
    have hcx : Nat.card ↥(commV (Subgroup.zpowers x)) = 4 := by rw [hXz]; exact hX4
    have hcy : Nat.card ↥(commV (Subgroup.zpowers y)) = 4 := by rw [hYz]; exact cfg.adm.h4
    have hYB : Y ≤ X₁ := hX₁.1
    have hxN := cfg.normalizes_of_lift hV htY ht2 hX₁ hn D hxX
    rcases D.normalizer_dichotomy hV hn hR hxN hx3 hcx with hcen | hxB
    ·
      have hxy : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a := by
        intro a ha b hb
        rw [← hXz] at ha
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have hbx : Commute b x := hcen b (hYB hb)
        exact ((hbx.symm).zpow_left m).eq
      exact ⟨isZ3E9A4A5_of_commute hX3 h3 hxy, Or.inl hxy⟩
    ·
      have hyB : y ∈ X₁ := hYB hy
      have hXB : X ≤ X₁ := by rw [← hXz]; exact Subgroup.zpowers_le.mpr hxB
      have hf : Function.Injective D.θ := (injective_iff_map_eq_one _).mpr hR
      have c1 := D.isThreeCycle_of_mem hV hxB hx3 hcx
      have c2 := D.isThreeCycle_of_mem hV hyB (hY3 y hy) hcy
      have hpair : IsZ3E9A4A5 ↥(X ⊔ Y) := by
        refine isZ3E9A4A5_of_subgroup_hom hXB hYB D.θ hf c1 c2 ?_ ?_
        · rw [← hXz, zpowers_subgroupOf_eq hxB, MonoidHom.map_zpowers]
        · rw [← hYz, zpowers_subgroupOf_eq hyB, MonoidHom.map_zpowers]
      exact ⟨hpair, Or.inr ⟨X₁, hperf, hX₁⟩⟩

end Block

end CFSG.CGT.PushingUpLit.CGT6
