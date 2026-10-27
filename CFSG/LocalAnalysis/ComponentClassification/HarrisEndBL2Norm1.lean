module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Dih

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.eq_or_eq_of_card_le_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (h2 : Nat.card H ≤ 2) {a b c : G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hab : a ≠ b) :
    c = a ∨ c = b := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective (fun k : Fin 3 =>
      (![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] : Fin 3 → H) k) := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem EndB.orderOf_pow_half {G : Type*} [Group G] {v : G} {k : ℕ} (hk : orderOf v = 2 ^ k)
    (hv : v ≠ 1) : orderOf (v ^ (orderOf v / 2)) = 2 := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk hv
    · exact h0
  have hhalf : orderOf v / 2 = 2 ^ (k - 1) := by
    rw [hk, show k = (k - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ two_pos,
      show k - 1 + 1 - 1 = k - 1 by omega]
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, hhalf, ← pow_succ, show k - 1 + 1 = k by omega, ← hk, pow_orderOf_eq_one]
  · rw [hhalf]
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem z_mem_M (_hc : L2Ctx hs W) :
    z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
  K_le_centralizer_beta i j hs.lemma45.z_mem.2

theorem zBar_mem_layer (hc : L2Ctx hs W) :
    (QuotientGroup.mk ⟨z, hc.z_mem_M⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
  hs.KBar_le_layer ⟨⟨z, hc.z_mem_M⟩, hs.lemma45.z_mem.2, rfl⟩

theorem z_mem_W (hc : L2Ctx hs W) : z ∈ W :=
  hc.T_le (mem_sup_left (mem_sup_right hs.setup.z_mem))

theorem t_mem_W (hc : L2Ctx hs W) : t ∈ W :=
  hc.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))

theorem conjOn_zBar_ne_one (hc : L2Ctx hs W) :
    conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (QuotientGroup.mk ⟨z, hc.z_mem_M⟩) ≠ 1 := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have := hc.simple
  intro h1
  rw [conjOn_eq_one_iff] at h1
  have hKnab := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar hc.h412)
  have hCE := centralizer_inf_layer_eq_bot hs.KBar_le_layer hKnab
  have hz1 : (QuotientGroup.mk ⟨z, hc.z_mem_M⟩ : MBar β) = 1 := by
    have : (QuotientGroup.mk ⟨z, hc.z_mem_M⟩ : MBar β) ∈
        centralizer (layer (MBar β) : Set (MBar β)) ⊓ layer (MBar β) := ⟨h1, hc.zBar_mem_layer⟩
    rwa [hCE, mem_bot] at this
  have := mk_injOn hc.sylow.le hc.sylow.isPGroup hc.z_mem_W (one_mem W) (by rw [hz1]; rfl)
  exact hs.setup.z_ne_one this

theorem _root_.CFSG.ComponentClassification.HarrisLit.EndB.mem_centralizer_cases {G : Type*}
    [Group G] [Finite G] {P R : Subgroup G} {ζ τ v₀ : G}
    (hZ2 : Nat.card ↥(R ⊓ centralizer (R : Set G)) ≤ 2)
    (hζZ : ζ ∈ R ⊓ centralizer (R : Set G)) (hζ1 : ζ ≠ 1) (hv₀2 : orderOf v₀ = 2)
    (hv₀c : ∀ c ∈ R, c * v₀ = v₀ * c)
    (hCR : P ⊓ centralizer (R : Set G) = (R ⊓ centralizer (R : Set G)) ⊔ zpowers v₀)
    (hτ : τ ∈ P ⊓ centralizer (R : Set G)) (hτR : τ ∉ R) {α : G}
    (hα : α ∈ P ⊓ centralizer (R : Set G)) : α = 1 ∨ α = ζ ∨ α = τ ∨ α = ζ * τ := by
  have hZcases : ∀ c ∈ R ⊓ centralizer (R : Set G), c = 1 ∨ c = ζ := fun c hc' =>
    EndB.eq_or_eq_of_card_le_two hZ2 (one_mem _) hζZ hc' (Ne.symm hζ1)
  have hζ2 : ζ * ζ = 1 := by
    rcases hZcases (ζ * ζ) (mul_mem hζZ hζZ) with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one ζ).symm)) hζ1
  have hcomm : ∀ (n : ℤ), ∀ c ∈ R, v₀ ^ n * c = c * v₀ ^ n := fun n c hc' =>
    ((Commute.zpow_right (hv₀c c hc') n).eq).symm
  have hv₀N : zpowers v₀ ≤ normalizer ((R ⊓ centralizer (R : Set G) : Subgroup G) : Set G) := by
    intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hcZ
      rw [hcomm n c hcZ.1, mul_inv_cancel_right]
      exact hcZ
    · intro hcZ
      have hd := hcomm n _ hcZ.1
      have hceq : v₀ ^ n * c * (v₀ ^ n)⁻¹ = c := by
        calc v₀ ^ n * c * (v₀ ^ n)⁻¹ =
              (v₀ ^ n)⁻¹ * (v₀ ^ n * (v₀ ^ n * c * (v₀ ^ n)⁻¹)) := by group
          _ = (v₀ ^ n)⁻¹ * ((v₀ ^ n * c * (v₀ ^ n)⁻¹) * v₀ ^ n) := by rw [hd]
          _ = c := by group
      rw [← hceq]
      exact hcZ
  have hdecomp : ∀ x ∈ P ⊓ centralizer (R : Set G),
      ∃ y ∈ zpowers v₀, ∃ c ∈ R ⊓ centralizer (R : Set G), x = y * c := by
    intro x hx
    rw [hCR, sup_comm] at hx
    have hx' : x ∈ ((zpowers v₀ : Set G) * ((R ⊓ centralizer (R : Set G) : Subgroup G) :
        Set G)) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hv₀N]
      exact hx
    obtain ⟨y, hy, c, hc', rfl⟩ := hx'
    exact ⟨y, hy, c, hc', rfl⟩
  obtain ⟨y, hy, c, hcZ, hτyc⟩ := hdecomp τ hτ
  have hyv : y = v₀ := by
    rcases eq_one_or_eq_of_mem_zpowers_two hv₀2 hy with h | h
    · exfalso
      rw [h, one_mul] at hτyc
      exact hτR (hτyc ▸ hcZ.1)
    · exact h
  rw [hyv] at hτyc
  have hτζ : τ * ζ = ζ * τ := (mem_centralizer_iff.mp hτ.2 ζ hζZ.1).symm
  obtain ⟨y', hy', c', hc'Z, rfl⟩ := hdecomp α hα
  have hv₀eq : v₀ = τ * c := by
    rw [hτyc, mul_assoc]
    rcases hZcases c hcZ with h' | h'
    · rw [h', mul_one, mul_one]
    · rw [h', hζ2, mul_one]
  rcases eq_one_or_eq_of_mem_zpowers_two hv₀2 hy' with h | h
  · rw [h, one_mul]
    rcases hZcases c' hc'Z with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rw [h, hv₀eq]
    rcases hZcases c hcZ with h1 | h1 <;> rcases hZcases c' hc'Z with h2 | h2 <;>
      rw [h1, h2]
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_one, mul_one])))
    · exact Or.inr (Or.inr (Or.inr (by rw [mul_one, hτζ])))
    · exact Or.inr (Or.inr (Or.inr (by rw [mul_one, hτζ])))
    · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, hζ2, mul_one])))

theorem mem_centralizer_R (hKC : AutPSL2CentralizerInput) (hFC : AutPSL2FieldCentralizerInput)
    (hc : L2Ctx hs W) {v : MulAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (hv : SylowAutData ((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
      W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) v)
    {α : MulAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))}
    (hα : α ∈ (barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) W).map
      (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
      centralizer (((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} :
      Set X)) W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ⊓
        innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) : Subgroup _) : Set _)) :
    α = 1 ∨
      α = conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨z, hc.z_mem_M⟩) ∨
      α = conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∨
      α = conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
        (QuotientGroup.mk ⟨z, hc.z_mem_M⟩) *
        conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, ⟨e⟩⟩ := hv.dihedral
  have hzZW : z ∈ W ⊓ centralizer (W : Set X) := by
    rw [hc.center_eq hKC]
    exact subset_closure (Set.mem_insert_of_mem _ rfl)
  have hP2 : IsPGroup 2 ((barOf (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
      W).map (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))) :=
    ((isSylowOf_barOf hc.sylow).isPGroup).map _
  have hv1 : v ≠ 1 := fun h => hv.not_mem_inn (by rw [h]; exact one_mem _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP2 ⟨v, hv.mem⟩
  rw [Subgroup.orderOf_mk] at hk
  refine EndB.mem_centralizer_cases (EndB.dih_card_center_le (by omega) e) ⟨⟨⟨_,
    mk_mem_barOf hc.z_mem_M hc.z_mem_W, rfl⟩, ⟨⟨_, hc.zBar_mem_layer⟩,
      (EndB.conjOn_of_mem ⟨_, hc.zBar_mem_layer⟩).symm⟩⟩, ?_⟩ hc.conjOn_zBar_ne_one
    (EndB.orderOf_pow_half hk hv1) hv.comm_v₀ hv.centralizer_R ⟨⟨_,
      mk_mem_barOf (hs.setup.t_mem_centralizer_beta i j) hc.t_mem_W, rfl⟩,
      mem_centralizer_iff.mpr fun r hr => (hc.tau_comm hFC hr).symm⟩ (fun h => hc.out h.2) hα
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro r ⟨⟨g, hg, rfl⟩, -⟩
  obtain ⟨x, hxW, rfl⟩ := mem_barOf.mp hg
  rw [← map_mul, ← map_mul]
  congr 1
  have hxz : (x : X) * z = z * x := ((mem_centralizer_iff.mp hzZW.2) _ hxW)
  change (QuotientGroup.mk (x * ⟨z, hc.z_mem_M⟩) : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
    QuotientGroup.mk (⟨z, hc.z_mem_M⟩ * x)
  congr 1
  exact Subtype.ext hxz

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
