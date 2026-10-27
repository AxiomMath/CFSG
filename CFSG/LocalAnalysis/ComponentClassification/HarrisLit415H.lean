module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Nilp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415W0Sylow
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem isPGroup_quot_iff {G : Type*} [Group G] {N : Subgroup G} [N.Normal] :
    IsPGroup 2 (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ (2 ^ k) ∈ N := by
  constructor
  · intro h g
    obtain ⟨k, hk⟩ := h (QuotientGroup.mk g)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

theorem isPGroup_quot_of_injective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : B →* A) (hf : Function.Injective f) (hA : IsPGroup 2 (A ⧸ pPrimeCore 2 A)) :
    IsPGroup 2 (B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((pPrimeCore 2 A).comap f).Normal := by
    have := pPrimeCore_normal (p := 2) (G := A)
    infer_instance
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 A).comap f)) := by
    have h1 : Nat.card ((pPrimeCore 2 A).comap f) ∣ Nat.card (pPrimeCore 2 A) := by
      rw [← Subgroup.card_map_of_injective hf]
      exact Subgroup.card_dvd_of_le (map_comap_le _ _)
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hle : (pPrimeCore 2 A).comap f ≤ pPrimeCore 2 B := le_sSup ⟨hN, hcop⟩
  rw [isPGroup_quot_iff] at hA ⊢
  intro b
  obtain ⟨k, hk⟩ := hA (f b)
  exact ⟨k, hle (by rw [mem_comap, map_pow]; exact hk)⟩

namespace IsProd

variable {G : Type} [Group G] [Finite G] {E K₁ K₂ : Subgroup G} {s : G}

theorem isPGroup_centralizer (h : IsProd E K₁ K₂ s) (hE : E.Normal)
    (hI : AutPSL2InvolutionCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥K₁ .PSL 2 p n) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hCQ : centralizer (E : Set G) ≤ Q) (hodd : ∀ g : G, Odd (orderOf g) → ∀ x ∈ Q, g * x = x * g)
    {y : G} (hyK : y ∈ K₁) (hy : orderOf y = 2) :
    IsPGroup 2 (↥(centralizer {y} ⊓ centralizer (K₂ : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer {y} ⊓ centralizer (K₂ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer {y} ⊓ centralizer (K₂ : Set G) with hCdef
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  have hCN : C ≤ normalizer (K₁ : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_map]
    exact h.map_K₁_of_comm hE hyK hy1 (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).1)
  let ρ : ↥C →* MulAut ↥K₁ := (normalizerConj K₁).comp (inclusion hCN)
  have hρ : ∀ (c : ↥C) (l : ↥K₁), ((ρ c l : ↥K₁) : G) = (c : G) * l * (c : G)⁻¹ :=
    fun _ _ => rfl
  have hfix : ∀ c : ↥C, ρ c ∈ MulAction.stabilizer (MulAut ↥K₁) (⟨y, hyK⟩ : ↥K₁) := by
    intro c
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change ((ρ c ⟨y, hyK⟩ : ↥K₁) : G) = y
    rw [hρ]
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).1
    calc (c : G) * y * (c : G)⁻¹ = y * c * (c : G)⁻¹ := by rw [h1]
      _ = y := by group
  let ρ' : ↥C →* ↥(MulAction.stabilizer (MulAut ↥K₁) (⟨y, hyK⟩ : ↥K₁)) := ρ.codRestrict _ hfix
  have hker : ∀ c ∈ ρ'.ker, (c : G) ∈ Q := by
    intro c hc
    have hρ1 : ρ c = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    apply hCQ
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hx
    have h1 : (c : G) * a * (c : G)⁻¹ = a := by
      rw [← hρ c ⟨a, ha⟩, hρ1]
      rfl
    have h2 : b * c = c * b := (Subgroup.mem_centralizer_iff.mp (mem_inf.mp c.2).2) b hb
    calc a * b * c = a * c * b := by rw [mul_assoc, h2, ← mul_assoc]
      _ = c * a * (c : G)⁻¹ * c * b := by rw [h1]
      _ = c * (a * b) := by group
  have hS := hI ↥K₁ p n hp hp2 hlie ⟨y, hyK⟩ (by rw [Subgroup.orderOf_mk]; exact hy)
  have hR : IsPGroup 2 (↥ρ'.range ⧸ pPrimeCore 2 ↥ρ'.range) :=
    isPGroup_quot_of_injective ρ'.range.subtype ρ'.range.subtype_injective hS
  have hCK : IsPGroup 2 ((↥C ⧸ ρ'.ker) ⧸ pPrimeCore 2 (↥C ⧸ ρ'.ker)) :=
    isPGroup_quot_of_injective (QuotientGroup.quotientKerEquivRange ρ').toMonoidHom
      (QuotientGroup.quotientKerEquivRange ρ').injective hR
  refine isPGroup_quot_of_central (P := ρ'.ker) ?_ hCK ?_
  · intro g
    obtain ⟨k, hk⟩ := hQ ⟨((g : ↥C) : G), hker g g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  · intro g hg x hx
    apply Subtype.ext
    exact hodd g (by rwa [Subgroup.orderOf_coe]) x (hker x hx)

end IsProd

theorem isPGroup_centralizer_K₂_of {X : Type} [Group X] [Finite X] {β t z₁ : X}
    {Kb₁ Kb₂ : Subgroup (MBar β)} (htM : t ∈ centralizer ({β} : Set X))
    (hprod : IsProd (layer (MBar β)) Kb₁ Kb₂ (QuotientGroup.mk ⟨t, htM⟩))
    (hI : AutPSL2InvolutionCentralizerInput) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlie : Blueprint.LieModel ↥Kb₁ .PSL 2 p n)
    (hQC : centralizer ((layer (MBar β) : Subgroup (MBar β)) : Set (MBar β)) ≤
      pCore 2 (MBar β))
    (hodd : closure {x : MBar β | Odd (orderOf x)} ≤
      centralizer (pCore 2 (MBar β) : Set (MBar β)))
    (hz₁M : z₁ ∈ centralizer ({β} : Set X))
    (hzb : (QuotientGroup.mk ⟨z₁, hz₁M⟩ : MBar β) ∈ Kb₁)
    (hzo : orderOf (QuotientGroup.mk ⟨z₁, hz₁M⟩ : MBar β) = 2)
    {K₂ : Subgroup X}
    (hK₂map : (K₂.subgroupOf (centralizer {β})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))) = Kb₂) :
    IsPGroup 2 (↥(centralizer {z₁} ⊓ centralizer {β} ⊓ centralizer (K₂ : Set X)) ⧸
      pPrimeCore 2 ↥(centralizer {z₁} ⊓ centralizer {β} ⊓ centralizer (K₂ : Set X))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer ({β} : Set X) with hMdef
  set H := centralizer {z₁} ⊓ centralizer {β} ⊓ centralizer (K₂ : Set X) with hHdef
  have hE : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hCb := hprod.isPGroup_centralizer hE hI hp hp2 hlie pCore_isPGroup hQC
    (fun g hg x hx => ((mem_centralizer_iff.mp
      (hodd (subset_closure (show g ∈ {x : MBar β | Odd (orderOf x)} from hg)))) x hx).symm)
    hzb hzo
  have hHM : H ≤ M := fun x hx => (mem_inf.mp (mem_inf.mp hx).1).2
  have himg : (H.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
      centralizer {(QuotientGroup.mk ⟨z₁, hz₁M⟩ : MBar β)} ⊓
        centralizer (Kb₂ : Set (MBar β)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : X) ∈ H := hx
    have hxz : (x : X) * z₁ = z₁ * x :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp hx').1).1
    have hxK : ∀ k ∈ K₂, k * x = x * k := mem_centralizer_iff.mp (mem_inf.mp hx').2
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hxz
    · rw [mem_centralizer_iff]
      intro k hk
      rw [← hK₂map] at hk
      obtain ⟨k, hk, rfl⟩ := hk
      have hk' : (k : X) ∈ K₂ := hk
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hxK _ hk')
  have h1 := isPGroup_quot_of_injective (inclusion himg) (inclusion_injective himg) hCb
  obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥M)) GSThmB.OddQuot.not_two_dvd_card_ker (H.subgroupOf M)
  have h2 := h1.of_equiv e.symm
  exact isPGroup_quot_of_injective (subgroupOfEquivOfLe hHM).symm.toMonoidHom
    (subgroupOfEquivOfLe hHM).symm.injective h2

end L415

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ} {hs : Setting46e t L p f S w z V i j}
  {Kb₁ Kb₂ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} {W : Subgroup X} {z₁ : X}

namespace Config415

variable (hc : Config415 hs Kb₁ Kb₂ W z₁)
include hc

theorem orderOf_mk_z₁ :
    orderOf (QuotientGroup.mk ⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 2 := by
  have hz₁1 : z₁ ≠ 1 := fun h1 => hc.z₁_ne (by rw [h1]; group)
  refine orderOf_eq_prime ?_ fun h1 => hz₁1 ?_
  · rw [← QuotientGroup.mk_pow]
    have : (⟨z₁, hc.isSylowOf_W.le hc.z₁_mem⟩ :
        ↥(centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hc.sq_z₁)
    rw [this, QuotientGroup.mk_one]
  · exact mk_injOn hc.isSylowOf_W.le hc.isSylowOf_W.isPGroup hc.z₁_mem (one_mem W)
      (h1.trans rfl)

theorem isPGroup_centralizer_K₂ (hI : AutPSL2InvolutionCentralizerInput)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    {K₂ : Subgroup X}
    (hK₂map : (K₂.subgroupOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
        ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) = Kb₂) :
    IsPGroup 2 (↥(centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
        centralizer (K₂ : Set X)) ⧸
      pPrimeCore 2 ↥(centralizer {z₁} ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ⊓
        centralizer (K₂ : Set X))) := by
  obtain ⟨e₁⟩ := hc.equiv₁
  have hlie := GSThmB.OddQuot.lieModel_of_equiv e₁.symm (hs.lieModel_KBar h412)
  have hQC : centralizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [h412.pCore_eq.1, h412.pCore_eq.2]
  exact L415.isPGroup_centralizer_K₂_of (hc.isSylowOf_W.le hc.t_mem_W) hc.prod hI hs.prime_p
    hs.p_ne_two hlie hQC h412.oddGenerated_le (hc.isSylowOf_W.le hc.z₁_mem)
    (hc.mk_z₁ _) hc.orderOf_mk_z₁ hK₂map

end Config415

end CFSG.ComponentClassification.HarrisLit
