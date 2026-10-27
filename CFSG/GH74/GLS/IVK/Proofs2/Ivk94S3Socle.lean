module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4D4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3KL
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

section Sylow

variable {H : Type} [Group H] [Finite H]

theorem card_two_subgroup_le (P : Sylow 2 H) {R : Subgroup H} (hR : IsPGroup 2 R) :
    Nat.card R ≤ Nat.card (P : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hRP'⟩ := hR.exists_le_sylow
  have h1 : Nat.card (P' : Subgroup H) = Nat.card (P : Subgroup H) := by
    rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
  rw [← h1]
  exact Subgroup.card_le_of_le hRP'

theorem not_dvd_of_card_le {K : Subgroup H} (P : Sylow 2 H) {n : ℕ}
    (hP : Nat.card (P : Subgroup H) ≤ 2 ^ n) : ¬ 2 ^ (n + 1) ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hd
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 hd
  have hRp : IsPGroup 2 (R.map K.subtype) := by
    refine IsPGroup.of_card (n := n + 1) ?_
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR]
  have hc : Nat.card (R.map K.subtype) = 2 ^ (n + 1) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR]
  have := card_two_subgroup_le P hRp
  rw [hc] at this
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h3 : 0 < 2 ^ n := by positivity
  omega


theorem all_two_elements_mem {K : Subgroup H} (hK : K.Normal) (P : Sylow 2 H)
    (hP : Nat.card (P : Subgroup H) ≤ 64) (h64 : 64 ∣ Nat.card K) :
    ∀ x : H, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 (n := 6) (by simpa using h64)
  have hRp : IsPGroup 2 (R.map K.subtype) := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR]
  obtain ⟨P', hRP'⟩ := hRp.exists_le_sylow
  have hcP' : Nat.card (P' : Subgroup H) = Nat.card (P : Subgroup H) := by
    rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
  have hcR : Nat.card (R.map K.subtype) = 64 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR]; norm_num
  have hPP' : (R.map K.subtype) = (P' : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hRP' (by rw [hcR, hcP']; omega)
  have hP'K : (P' : Subgroup H) ≤ K := by
    rw [← hPP']
    exact Subgroup.map_subtype_le _
  have hall : ∀ Q : Sylow 2 H, (Q : Subgroup H) ≤ K := by
    intro Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q
    rw [← hg, Sylow.coe_subgroup_smul]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have := hK.conj_mem a (hP'K ha) g
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  intro x ⟨k, hk⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
  have hxp : IsPGroup 2 (zpowers x) := by
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj]
  obtain ⟨Q, hxQ⟩ := hxp.exists_le_sylow
  exact hall Q (hxQ (mem_zpowers x))

theorem exists_conj_mem_sylow (P Q : Sylow 2 H) {a : H} (ha : a ∈ (Q : Subgroup H)) :
    ∃ g : H, g * a * g⁻¹ ∈ (P : Subgroup H) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨a, ha, by simp [MulAut.smul_def, MulAut.conj_apply]⟩

theorem z_mem_of_normal_inf_ne_bot {P : Sylow 2 H} {z : H}
    (hPz : zpowers z = (center ↥(P : Subgroup H)).map (P : Subgroup H).subtype)
    (hz2 : z * z = 1) {M : Subgroup H} (hM : M.Normal) (hne : M ⊓ (P : Subgroup H) ≠ ⊥) :
    z ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(P : Subgroup H) := P.isPGroup'.isNilpotent
  have hMP : (M.subgroupOf (P : Subgroup H)).Normal := Subgroup.Normal.subgroupOf hM _
  have hne' : M.subgroupOf (P : Subgroup H) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxM : (⟨x, hx.2⟩ : ↥(P : Subgroup H)) ∈ M.subgroupOf (P : Subgroup H) :=
      Subgroup.mem_subgroupOf.2 hx.1
    rw [h, Subgroup.mem_bot] at hxM
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxM
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(P : Subgroup H)) hne')
  have hxM : ((x : ↥(P : Subgroup H)) : H) ∈ M := Subgroup.mem_subgroupOf.1 x.2.1
  have hxz : ((x : ↥(P : Subgroup H)) : H) ∈ zpowers z := by
    rw [hPz]
    exact ⟨x, x.2.2, rfl⟩
  rcases mem_zpowers_of_sq hz2 hxz with h | h
  · exfalso
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rw [← h]
    exact hxM

theorem inf_sylow_ne_bot {K : Subgroup H} (hK : K.Normal) (P : Sylow 2 H) (heven : 2 ∣ Nat.card K) :
    K ⊓ (P : Subgroup H) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 heven
  have hw' : orderOf (w : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwp : IsPGroup 2 (zpowers (w : H)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hw']; norm_num
  obtain ⟨Q, hwQ⟩ := hwp.exists_le_sylow
  have hmem : (w : H) ∈ (Q : Subgroup H) := hwQ (mem_zpowers _)
  obtain ⟨g, hgw⟩ := exists_conj_mem_sylow P Q hmem
  intro h
  have hK' : g * (w : H) * g⁻¹ ∈ K := hK.conj_mem (w : H) w.2 g
  have h3 : g * (w : H) * g⁻¹ ∈ K ⊓ (P : Subgroup H) := ⟨hK', hgw⟩
  rw [h, Subgroup.mem_bot] at h3
  have h1 : (w : H) = 1 := by
    have h2 : g * (w : H) * g⁻¹ = 1 := h3
    calc (w : H) = g⁻¹ * (g * (w : H) * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have : w = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hw
  exact absurd hw (by norm_num)

end Sylow

section KL

variable {H : Type} [Group H] [Finite H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

omit [Finite H] in
theorem kl_of_normal {Yo : Subgroup H} {z : H}
    (S : Shape ↥Yo F₁ F₂) (hzS : (S.z : H) = z)
    (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3)
    {B : Subgroup H} (hB : B.Normal) {u : H} (huB : u ∈ B) (huY : u ∈ Yo)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    (∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) ∧ 32 ∣ Nat.card B ∧
      ∃ E : Subgroup H, E ≤ B ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
        Nat.card E = 8 := by
  have hA : (B.subgroupOf Yo).Normal := Subgroup.Normal.subgroupOf hB Yo
  have hu' : (⟨u, huY⟩ : ↥Yo) ∈ B.subgroupOf Yo := Subgroup.mem_subgroupOf.2 huB
  have hu'2 : (⟨u, huY⟩ : ↥Yo) * ⟨u, huY⟩ = 1 := Subtype.ext hu2
  have hu'1 : (⟨u, huY⟩ : ↥Yo) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hu'z : (⟨u, huY⟩ : ↥Yo) ≠ S.z := fun h => huz ((congrArg Subtype.val h).trans hzS)
  obtain ⟨hk₁, hk₂⟩ := S.kl h₁ h₂ hA hu' hu'2 hu'1 hu'z
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, ha4, hb4, hab⟩ := S.exists_noncomm₁ h₁
    exact ⟨(a : H), Subgroup.mem_subgroupOf.1 (hk₁ a ha ha4), (b : H),
      Subgroup.mem_subgroupOf.1 (hk₁ b hb hb4), fun h => hab (Subtype.ext h)⟩
  · obtain ⟨R, hR, hRx⟩ := S.exists_Q32 h₁ h₂
    have hRA : R ≤ B.subgroupOf Yo := by
      intro x hx
      obtain ⟨a, ha, b, hb, ha4, hb4, rfl⟩ := hRx x hx
      exact mul_mem (hk₁ a ha ha4) (hk₂ b hb hb4)
    have hRB : R.map Yo.subtype ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hRA hx)
    have := Subgroup.card_dvd_of_le hRB
    rwa [Subgroup.card_map_of_injective Yo.subtype_injective, hR] at this
  · have hodd₁ : Odd (Nat.card F₁) := by rw [h₁]; exact ⟨1, rfl⟩
    have hodd₂ : Odd (Nat.card F₂) := by rw [h₂]; exact ⟨1, rfl⟩
    obtain ⟨E, hEle, hEc, hE2, hE8⟩ := S.exists_elementary_eight hodd₁ hodd₂
    have hEA : E ≤ B.subgroupOf Yo := by
      intro x hx
      obtain ⟨a, ha, b, hb, ha4, hb4, rfl⟩ :=
        S.sq_one_mem_sup (hEle hx) (by rw [← pow_two]; exact hE2 x hx)
      exact mul_mem (hk₁ a ha ha4) (hk₂ b hb hb4)
    refine ⟨E.map Yo.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hEA hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hEc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hE2 x hx)
    · rw [Subgroup.card_map_of_injective Yo.subtype_injective, hE8]

end KL

section PCore2

variable {H : Type} [Group H] [Finite H]

theorem pCore_two_eq_bot_of_nonabelian {P : Sylow 2 H} {z u : H}
    (hPz : zpowers z = (center ↥(P : Subgroup H)).map (P : Subgroup H).subtype) (hz2 : z * z = 1)
    (hconj : IsConj z u)
    (hnab : ∀ B : Subgroup H, B.Normal → u ∈ B → ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) :
    pCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hTn : (pCore 2 H).Normal := pCore_normal
  have hTp : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  have hTP : pCore 2 H ≤ (P : Subgroup H) := fun q hq => IsPGroup.le_sylow_of_normal hTp P hq
  have hnilT : Group.IsNilpotent ↥(pCore 2 H) := hTp.isNilpotent
  let M : Subgroup H := pCore 2 H ⊓ centralizer ((pCore 2 H : Subgroup H) : Set H)
  have hcn : (centralizer ((pCore 2 H : Subgroup H) : Set H)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro t ht
    have h1 : g⁻¹ * t * g ∈ pCore 2 H := by
      simpa using hTn.conj_mem t ht g⁻¹
    have h2 := ha _ h1
    calc t * (g * a * g⁻¹) = g * ((g⁻¹ * t * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * t * g)) * g⁻¹ := by rw [h2]
      _ = g * a * g⁻¹ * t := by group
  have hMn : M.Normal := Subgroup.normal_inf_normal _ _
  have hMne : M ≠ ⊥ := by
    have hTne : (⊤ : Subgroup ↥(pCore 2 H)) ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro q hq
      have : (⟨q, hq⟩ : ↥(pCore 2 H)) ∈ (⊤ : Subgroup ↥(pCore 2 H)) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥(pCore 2 H)) hTne)
    intro hM
    apply hx
    have hxM : ((x : ↥(pCore 2 H)) : H) ∈ M := by
      refine Subgroup.mem_inf.2 ⟨(x : ↥(pCore 2 H)).2, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro t ht
      have := Subgroup.mem_center_iff.1 x.2.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    rw [hM, Subgroup.mem_bot] at hxM
    apply Subtype.ext
    apply Subtype.ext
    exact hxM
  have hMP : M ⊓ (P : Subgroup H) ≠ ⊥ := by
    have : M ⊓ (P : Subgroup H) = M := inf_eq_left.2 (inf_le_left.trans hTP)
    rwa [this]
  have hzM : z ∈ M := z_mem_of_normal_inf_ne_bot hPz hz2 hMn hMP
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have huM : u ∈ M := hg ▸ hMn.conj_mem z hzM g
  obtain ⟨a, ha, b, hb, hab⟩ := hnab M hMn huM
  apply hab
  have hbT : b ∈ pCore 2 H := hb.1
  have := Subgroup.mem_centralizer_iff.1 ha.2 b hbT
  exact this.symm

omit [Finite H] in
theorem layer_ne_bot_of_cores [Finite H] [Nontrivial H] (hO : pPrimeCore 2 H = ⊥) (hO₂ : pCore 2 H = ⊥) :
    layer H ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hL
  have hF := (LocalCores.generalized_fitting_minimal_normal (G := H)).2 inferInstance
  apply hF
  show fittingSubgroup H ⊔ layer H = ⊥
  rw [hL, sup_bot_eq, LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_eq_bot.2 fun p => ?_
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2]; exact hO₂
  · have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hpp⟩
    have hcop : Nat.Coprime 2 (Nat.card (pCore (p : ℕ) H)) := by
      obtain ⟨k, hk⟩ := (pCore_isPGroup (G := H) (p := (p : ℕ))).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hpp).2 (fun h => hp2 h.symm))
    have hle := CFSG.GroupTheory.le_pPrimeCore_of_normal (p := 2) (pCore_normal (p := (p : ℕ)) (G := H)) hcop
    rw [hO] at hle
    exact eq_bot_iff.2 hle

end PCore2

section Main

variable {H : Type} [Group H] [Finite H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

theorem card_shape_three {Y : Type} [Group Y] (S : Shape Y F₁ F₂) (h₁ : Nat.card F₁ = 3)
    (h₂ : Nat.card F₂ = 3) : Nat.card Y = 576 := by
  have h := shape_card_eq S
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h₁, h₂] at h
  rw [h]
  norm_num

theorem exists_socle_data {z u : H} {Yo : Subgroup H}
    (hYo : Yo = oPrimeResidualOf 2 (centralizer ({z} : Set H))) (hO : pPrimeCore 2 H = ⊥) (hrk : CFSG.pRank 2 H ≤ 3)
    (hz : orderOf z = 2) (hu : orderOf u = 2) (hzu : z ≠ u) (hconj : IsConj z u)
    (P : Sylow 2 H) (hPz : zpowers z = (center ↥(P : Subgroup H)).map (P : Subgroup H).subtype)
    (huP : u ∈ (P : Subgroup H))
    (S : Shape ↥Yo F₁ F₂) (hzS : (S.z : H) = z)
    (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3) :
    ∃ hzK : z ∈ layer H, IsSimpleGroup ↥(layer H) ∧ (∃ a b : ↥(layer H), a * b ≠ b * a) ∧
      3 ≤ CFSG.pRank 2 ↥(layer H) ∧ 32 ∣ Nat.card ↥(layer H) ∧ ¬ 128 ∣ Nat.card ↥(layer H) ∧
      (64 ∣ Nat.card ↥(layer H) → ∃ Y' : Subgroup ↥(layer H),
        Y' ≤ centralizer ({(⟨z, hzK⟩ : ↥(layer H))} : Set ↥(layer H)) ∧ Nat.card Y' = 576 ∧
        ∀ x ∈ centralizer ({(⟨z, hzK⟩ : ↥(layer H))} : Set ↥(layer H)),
          (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ Y') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hz ▸ pow_orderOf_eq_one z
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hu ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have : Nontrivial H := ⟨⟨z, 1, hz1⟩⟩
  have hYo576 : Nat.card ↥Yo = 576 := card_shape_three S h₁ h₂
  have hzC : ∀ x ∈ (P : Subgroup H), x * z = z * x := by
    intro x hx
    have hzm : z ∈ (center ↥(P : Subgroup H)).map (P : Subgroup H).subtype := by
      rw [← hPz]; exact mem_zpowers z
    obtain ⟨c, hc, hcz⟩ := hzm
    rw [← hcz]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨x, hx⟩)
  have hPY : (P : Subgroup H) ≤ Yo := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    rw [hYo]
    exact mem_oPrimeResidualOf_of_pow (Subgroup.mem_centralizer_singleton_iff.2 (hzC x hx))
      (k := k) (by simpa using congrArg Subtype.val hk)
  have hP64 : Nat.card (P : Subgroup H) ≤ 2 ^ 6 := by
    have hdvd : Nat.card (P : Subgroup H) ∣ 576 := hYo576 ▸ Subgroup.card_dvd_of_le hPY
    rw [Sylow.card_eq_multiplicity P] at hdvd ⊢
    by_contra hlt
    have h7 : 7 ≤ (Nat.card H).factorization 2 := by
      by_contra h
      apply hlt
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 7 ∣ 576 := (Nat.pow_dvd_pow 2 h7).trans hdvd
    omega
  have huY : u ∈ Yo := hPY huP
  have hnab : ∀ B : Subgroup H, B.Normal → u ∈ B → ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a :=
    fun B hB huB => (kl_of_normal S hzS h₁ h₂ hB huB huY hu2 hu1 (Ne.symm hzu)).1
  have hO₂ : pCore 2 H = ⊥ := pCore_two_eq_bot_of_nonabelian hPz hz2 hconj hnab
  have hne : layer H ≠ ⊥ := layer_ne_bot_of_cores hO hO₂
  obtain ⟨hs, hnabK⟩ := isSimpleGroup_layer hO hO₂ hne hrk
  have hKn : (layer H).Normal := by
    have := LocalCores.layer_characteristic (G := H)
    infer_instance
  have heven : 2 ∣ Nat.card (layer H) := by
    by_contra h
    have hcop : Nat.Coprime 2 (Nat.card (layer H)) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h
    have hle := CFSG.GroupTheory.le_pPrimeCore_of_normal (p := 2) hKn hcop
    rw [hO] at hle
    exact hne (eq_bot_iff.2 hle)
  have hzK : z ∈ layer H :=
    z_mem_of_normal_inf_ne_bot hPz hz2 hKn (inf_sylow_ne_bot hKn P heven)
  have huK : u ∈ layer H := by
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    exact hg ▸ hKn.conj_mem z hzK g
  obtain ⟨-, h32, E, hEK, hEc, hE2, hE8⟩ := kl_of_normal S hzS h₁ h₂ hKn huK huY hu2 hu1 (Ne.symm hzu)
  refine ⟨hzK, hs, hnabK, ?_, h32, ?_, ?_⟩
  ·
    refine le_pRank_two_of_comm_sq (V := E.subgroupOf (layer H)) ?_ ?_ (k := 3) ?_
    · intro x hx y hy
      rw [Subgroup.mem_subgroupOf] at hx hy
      exact Subtype.ext (hEc _ hx _ hy)
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subtype.ext (hE2 _ hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE8]
      norm_num
  · have := not_dvd_of_card_le (K := layer H) P hP64
    simpa using this
  · intro h64
    have hall := all_two_elements_mem hKn P (by simpa using hP64) h64
    have hYK : Yo ≤ layer H := by
      rw [hYo, oPrimeResidualOf_eq_closure']
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨-, k, hk⟩
      exact hall x ⟨k, hk⟩
    have hYC : Yo ≤ centralizer ({z} : Set H) := hYo ▸ Subgroup.map_subtype_le _
    refine ⟨Yo.subgroupOf (layer H), ?_, ?_, ?_⟩
    · intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 (hYC (Subgroup.mem_subgroupOf.1 hy))
      exact this
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv, hYo576]
    · intro x hx ⟨k, hk⟩
      rw [Subgroup.mem_subgroupOf]
      have hxC : (x : H) ∈ centralizer ({z} : Set H) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.1 hx
        exact congrArg Subtype.val this
      rw [hYo]
      exact mem_oPrimeResidualOf_of_pow hxC (k := k) (by simpa using congrArg Subtype.val hk)

end Main

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
