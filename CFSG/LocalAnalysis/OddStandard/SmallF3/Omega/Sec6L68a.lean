module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem eq_of_mul_inv_mem_center {A : Type*} [Group A]
    (hperf : commutator A = ⊤) (φ : A →* A)
    (h : ∀ a, φ a * a⁻¹ ∈ Subgroup.center A) : ∀ a, φ a = a := by
  let f : A →* Subgroup.center A :=
  { toFun := fun a => ⟨φ a * a⁻¹, h a⟩
    map_one' := by ext; simp
    map_mul' := by
      intro a b
      ext
      simp only [map_mul, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_mk]
      have hc : a⁻¹ * (φ b * b⁻¹) = (φ b * b⁻¹) * a⁻¹ :=
        Subgroup.mem_center_iff.mp (h b) a⁻¹
      rw [show (φ a * φ b) * (b⁻¹ * a⁻¹) = φ a * ((φ b * b⁻¹) * a⁻¹) by group,
        ← hc]
      group }
  have hle : commutator A ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (f b).2 (f a)))
  have hker : f.ker = ⊤ := le_antisymm le_top (hperf ▸ hle)
  intro a
  have ha : a ∈ f.ker := by rw [hker]; exact Subgroup.mem_top a
  have hfa : f a = 1 := MonoidHom.mem_ker.mp ha
  exact mul_inv_eq_one.mp (congrArg Subtype.val hfa)

theorem sec68_exists_sq [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hcyc : IsCyclic P)
    {t : G} (htP : t ∈ P) (ht2 : orderOf t = 2) (hne : P ≠ zpowers t) :
    ∃ x ∈ P, x * x = t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hcardP2 : 2 < Nat.card P := by
    by_contra h
    push Not at h
    have hzp : Nat.card (Subgroup.zpowers t) = 2 := by
      rw [Nat.card_zpowers, ht2]
    exact hne (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem htP)
      (by omega)).symm
  have hk2 : 2 ≤ k := by
    have hlt : 2 < 2 ^ k := by rwa [← hk]
    by_contra h
    push Not at h
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl <;> norm_num at hlt
  haveI : IsCyclic ↥P := hcyc
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥P)
  have htop : Subgroup.zpowers γ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact hγ x
  have horder : orderOf γ = 2 ^ k := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top]
    exact hk
  have ht'mem : (⟨t, htP⟩ : ↥P) ∈ Subgroup.zpowers γ := hγ ⟨t, htP⟩
  rw [mem_zpowers_iff_mem_range_orderOf] at ht'mem
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp ht'mem
  have hpow : γ ^ (2 * m) = 1 := by
    have hsq : (γ ^ m) ^ 2 = 1 := by
      have ho : orderOf (γ ^ m) = 2 := by rw [hm, Subgroup.orderOf_mk t htP, ht2]
      simpa [ho] using pow_orderOf_eq_one (γ ^ m)
    rwa [← pow_mul, Nat.mul_comm] at hsq
  have hdvd : 2 ^ k ∣ 2 * m := by
    have := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rwa [horder] at this
  have h2m : 2 ∣ m := by
    have h4k : (4 : ℕ) ∣ 2 ^ k := by
      refine ⟨2 ^ (k - 2), ?_⟩
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have h4' : 2 * 2 ∣ 2 * m := by simpa using h4k.trans hdvd
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h4'
  obtain ⟨j, hj⟩ := h2m
  refine ⟨(γ : G) ^ j, pow_mem γ.2 j, ?_⟩
  have hcoe : (γ : G) ^ m = t := by
    have := congrArg Subtype.val hm
    simpa [Subgroup.coe_pow] using this
  calc (γ : G) ^ j * (γ : G) ^ j = (γ : G) ^ (j + j) := by rw [← pow_add]
    _ = (γ : G) ^ m := by rw [hj, show j + j = 2 * j by omega]
    _ = t := hcoe

theorem sec68_exists_sylow_ge [Finite G] {B H : Subgroup G} (hB : IsPGroup 2 B) (hBH : B ≤ H) :
    ∃ P : Subgroup G, IsSylow2Of P H ∧ B ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB' : IsPGroup 2 (B.subgroupOf H) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q, hBQ⟩ := hB'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥H).map H.subtype, isSylow2Of_map_sylow Q, ?_⟩
  intro b hb
  have hbQ : (⟨b, hBH hb⟩ : ↥H) ∈ (Q : Subgroup ↥H) :=
    hBQ (by rw [Subgroup.mem_subgroupOf]; exact hb)
  exact Subgroup.mem_map_of_mem H.subtype hbQ

theorem sec68_sq_mem_centralizer [Finite G] {L : Subgroup G} (hL : IsOm6M L) {s : G} {n : ℕ}
    {ε : ℤˣ} {r : ℕ} {α : ℤˣ} (h : InducesTypeSome L s n ε r α) :
    s * s ∈ centralizer (L : Set G) := by
  obtain ⟨V, hAdd, hMod, hFin, Q, _hQ, e, x, _hfin, _hsign, hvia, htype⟩ := h
  letI := hAdd
  letI := hMod
  letI := hFin
  obtain ⟨y, hyx, _hyne, t, htt, _httype, hty⟩ := htype
  have hyy : y * y = 1 := by rw [← hty, ← map_mul, htt, map_one]
  have hsq : ∀ w : ProjOrth Q, projSimAct Q x (projSimAct Q x w) = w := by
    intro w
    rw [← hyx]
    simp only [projSimAct_projOrthToProjSim]
    rw [inv_eq_of_mul_eq_one_right hyy,
      show y * (y * w * y) * y = (y * y) * w * (y * y) by group, hyy]
    group
  let sn : G := s * s
  have hsn : sn ∈ Subgroup.normalizer (L : Set G) := by
    dsimp only [sn]; exact mul_mem hvia.1 hvia.1
  let φ : ↥L →* ↥L :=
  { toFun := fun l => ⟨sn * (l : G) * sn⁻¹,
      (Subgroup.mem_normalizer_iff.mp hsn (l : G)).mp l.2⟩
    map_one' := by ext; simp
    map_mul' := by
      intro a b
      ext
      simp only [Subgroup.coe_mk, Subgroup.coe_mul]
      group }
  have hcenter : ∀ l : ↥L, φ l * l⁻¹ ∈ Subgroup.center ↥L := by
    intro l
    have hl1 : s * (l : G) * s⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hvia.1 (l : G)).mp l.2
    have hl2 : s * (s * (l : G) * s⁻¹) * s⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hvia.1 (s * (l : G) * s⁻¹)).mp hl1
    let l₁ : ↥L := ⟨s * (l : G) * s⁻¹, hl1⟩
    let l₂ : ↥L := ⟨s * (s * (l : G) * s⁻¹) * s⁻¹, hl2⟩
    have he1 := hvia.2 l l₁ rfl
    have he2 := hvia.2 l₁ l₂ rfl
    have heq : e (QuotientGroup.mk l₂) = e (QuotientGroup.mk l) := by
      apply Subtype.ext
      rw [he2, he1, hsq]
    have hmk : QuotientGroup.mk l₂ = QuotientGroup.mk l := e.injective heq
    have hmem : l₂ / l ∈ Subgroup.center ↥L := QuotientGroup.eq_iff_div_mem.mp hmk
    have hφ : φ l = l₂ := by
      apply Subtype.ext
      change sn * (l : G) * sn⁻¹ = s * (s * (l : G) * s⁻¹) * s⁻¹
      dsimp only [sn]; group
    rw [hφ]
    simpa [div_eq_mul_inv] using hmem
  have hfix := eq_of_mul_inv_mem_center (Group.isPerfect_def.mp hL.1.1) φ hcenter
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hconj : sn * l * sn⁻¹ = l := by
    have h := congrArg (fun z : ↥L => (z : G)) (hfix ⟨l, hl⟩)
    change sn * l * sn⁻¹ = l at h
    exact h
  have hcomm : (s * s) * l = l * (s * s) := by
    have hc : (s * s) * l * (s * s)⁻¹ = l := by simpa [sn] using hconj
    calc (s * s) * l = (s * s) * l * (s * s)⁻¹ * (s * s) := by group
      _ = l * (s * s) := by rw [hc]
  exact hcomm.symm

theorem sec68_isOm6M_conjugate {L : Subgroup G} (hL : IsOm6M L) (g : G) :
    IsOm6M (CFSG.conjugate L g) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective) hL.1
  · exact lieModel_quotient_oddCore_conjugate g hL.2

theorem sec68_trans {N : Subgroup G} {T : Set G} {t p : G} (htT : t ∈ T) (hpT : p ∈ T)
    (htp : t ≠ p) (h3 : ∃ q ∈ T, q ≠ t ∧ q ≠ p)
    (h₁ : ∀ a ∈ T, a ≠ t → ∀ b ∈ T, b ≠ t →
      ∃ n ∈ N, n * t * n⁻¹ = t ∧ n * a * n⁻¹ = b)
    (h₂ : ∀ a ∈ T, a ≠ p → ∀ b ∈ T, b ≠ p →
      ∃ n ∈ N, n * p * n⁻¹ = p ∧ n * a * n⁻¹ = b) :
    ∀ a ∈ T, ∃ n ∈ N, n * t * n⁻¹ = a := by
  intro a haT
  by_cases hat : a = t
  · exact ⟨1, N.one_mem, by rw [hat]; group⟩
  · by_cases hap : a = p
    · obtain ⟨q, hqT, hqt, hqp⟩ := h3
      obtain ⟨n₁, hn₁N, _, hn₁t⟩ := h₂ t htT htp q hqT hqp
      obtain ⟨n₂, hn₂N, _, hn₂q⟩ := h₁ q hqT hqt p hpT htp.symm
      refine ⟨n₂ * n₁, mul_mem hn₂N hn₁N, ?_⟩
      rw [show n₂ * n₁ * t * (n₂ * n₁)⁻¹ = n₂ * (n₁ * t * n₁⁻¹) * n₂⁻¹ by group,
        hn₁t, hn₂q, hap]
    · obtain ⟨n, hnN, _, hnt⟩ := h₂ t htT htp a haT hap
      exact ⟨n, hnN, hnt⟩

theorem sec68_conjTwoTrans {N : Subgroup G} {T : Set G} {t p : G}
    (hT : ∀ n ∈ N, ∀ a ∈ T, n * a * n⁻¹ ∈ T) (htT : t ∈ T) (hpT : p ∈ T) (htp : t ≠ p)
    (h3 : ∃ q ∈ T, q ≠ t ∧ q ≠ p)
    (h₁ : ∀ a ∈ T, a ≠ t → ∀ b ∈ T, b ≠ t →
      ∃ n ∈ N, n * t * n⁻¹ = t ∧ n * a * n⁻¹ = b)
    (h₂ : ∀ a ∈ T, a ≠ p → ∀ b ∈ T, b ≠ p →
      ∃ n ∈ N, n * p * n⁻¹ = p ∧ n * a * n⁻¹ = b) :
    ConjTwoTransOn N T := by
  refine ⟨hT, ?_⟩
  have htrans : ∀ a ∈ T, ∃ n ∈ N, n * t * n⁻¹ = a := sec68_trans htT hpT htp h3 h₁ h₂
  have hstab : ∀ c ∈ T, ∀ a ∈ T, a ≠ c → ∀ b ∈ T, b ≠ c →
      ∃ n ∈ N, n * c * n⁻¹ = c ∧ n * a * n⁻¹ = b := by
    intro c hcT a haT hac b hbT hbc
    by_cases hct : c = t
    · rw [hct] at hac hbc ⊢
      exact h₁ a haT hac b hbT hbc
    · by_cases hcp : c = p
      · rw [hcp] at hac hbc ⊢
        exact h₂ a haT hac b hbT hbc
      · obtain ⟨m, hmN, _, hmp⟩ := h₁ p hpT htp.symm c hcT hct
        have ha'T : m⁻¹ * a * m ∈ T := by
          simpa using hT m⁻¹ (N.inv_mem hmN) a haT
        have hb'T : m⁻¹ * b * m ∈ T := by
          simpa using hT m⁻¹ (N.inv_mem hmN) b hbT
        have ha'p : m⁻¹ * a * m ≠ p := by
          intro h'
          apply hac
          calc a = m * (m⁻¹ * a * m) * m⁻¹ := by group
            _ = m * p * m⁻¹ := by rw [h']
            _ = c := hmp
        have hb'p : m⁻¹ * b * m ≠ p := by
          intro h'
          apply hbc
          calc b = m * (m⁻¹ * b * m) * m⁻¹ := by group
            _ = m * p * m⁻¹ := by rw [h']
            _ = c := hmp
        obtain ⟨n, hnN, hnp, hna⟩ :=
          h₂ (m⁻¹ * a * m) ha'T ha'p (m⁻¹ * b * m) hb'T hb'p
        have hmc : m⁻¹ * c * m = p := by rw [← hmp]; group
        refine ⟨m * n * m⁻¹, mul_mem (mul_mem hmN hnN) (N.inv_mem hmN), ?_, ?_⟩
        · calc m * n * m⁻¹ * c * (m * n * m⁻¹)⁻¹
              = m * (n * (m⁻¹ * c * m) * n⁻¹) * m⁻¹ := by group
            _ = m * (n * p * n⁻¹) * m⁻¹ := by rw [hmc]
            _ = m * p * m⁻¹ := by rw [hnp]
            _ = c := hmp
        · calc m * n * m⁻¹ * a * (m * n * m⁻¹)⁻¹
              = m * (n * (m⁻¹ * a * m) * n⁻¹) * m⁻¹ := by group
            _ = m * (m⁻¹ * b * m) * m⁻¹ := by rw [hna]
            _ = b := by group
  intro a haT b hbT c hcT d hdT hab hcd
  obtain ⟨na, hnaN, hnat⟩ := htrans a haT
  obtain ⟨nc, hncN, hnct⟩ := htrans c hcT
  let n₁ : G := nc * na⁻¹
  have hn₁N : n₁ ∈ N := by dsimp [n₁]; exact mul_mem hncN (N.inv_mem hnaN)
  have hn₁a : n₁ * a * n₁⁻¹ = c := by
    have hna : na⁻¹ * a * na = t := by rw [← hnat]; group
    calc n₁ * a * n₁⁻¹ = nc * (na⁻¹ * a * na) * nc⁻¹ := by dsimp [n₁]; group
      _ = nc * t * nc⁻¹ := by rw [hna]
      _ = c := hnct
  have hb'T : n₁ * b * n₁⁻¹ ∈ T := hT n₁ hn₁N b hbT
  have hb'c : n₁ * b * n₁⁻¹ ≠ c := by
    intro h
    apply hab
    have h2 : n₁ * b * n₁⁻¹ = n₁ * a * n₁⁻¹ := by rw [h, hn₁a]
    exact (mul_left_cancel (mul_right_cancel h2)).symm
  obtain ⟨n₂, hn₂N, hn₂c, hn₂b⟩ :=
    hstab c hcT (n₁ * b * n₁⁻¹) hb'T hb'c d hdT hcd.symm
  refine ⟨n₂ * n₁, mul_mem hn₂N hn₁N, ?_, ?_⟩
  · calc n₂ * n₁ * a * (n₂ * n₁)⁻¹
        = n₂ * (n₁ * a * n₁⁻¹) * n₂⁻¹ := by group
      _ = n₂ * c * n₂⁻¹ := by rw [hn₁a]
      _ = c := hn₂c
  · calc n₂ * n₁ * b * (n₂ * n₁)⁻¹
        = n₂ * (n₁ * b * n₁⁻¹) * n₂⁻¹ := by group
      _ = d := hn₂b

end CFSG.OddStandard.SmallF3.Omega
