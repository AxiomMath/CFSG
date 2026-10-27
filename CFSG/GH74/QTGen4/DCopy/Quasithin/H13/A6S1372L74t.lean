module

public import CFSG.Quasithin.H13.A6S1372L74t
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1357

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section U1

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem exists_U1_F4 (hhat : ¬ IsHatA6 L) :
    ∃ U₁ : Subgroup G, U₁ ≤ conjClosure S.V3 H ∧ fsuV1 T V ≤ U₁ ∧ S.V3 ≤ U₁ ∧
      (∀ g ∈ H, g ∈ Subgroup.normalizer (S.L1 : Set G) →
        g ∈ Subgroup.normalizer (U₁ : Set G)) ∧
      ∀ u ∈ U₁, (S.cL1 hhat : G) * u * (S.cL1 hhat : G)⁻¹ * u⁻¹ ∈ fsuV1 T V →
        u ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcH : c ∈ H := hL1H hcL
  have hV1V3 : fsuV1 T V ≤ S.V3 := S.V1_le_V2.trans S.V2_le_V3
  have hV1U : fsuV1 T V ≤ conjClosure S.V3 H := hV1V3.trans (le_conjClosure S.V3 H)
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hUab : ∀ x ∈ conjClosure S.V3 H, ∀ y ∈ conjClosure S.V3 H, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcU : c ∈ Subgroup.normalizer (conjClosure S.V3 H : Set G) := hHU hcH
  have hV1c : ∀ v ∈ fsuV1 T V, ∀ g ∈ H, g * v * g⁻¹ = v := fun v hv g hg =>
    hF.conj_eq_of_mem_V₁ hg hv
  have hsq : ∀ u ∈ conjClosure S.V3 H, u * u = 1 := fun u hu => by
    have := hab.2 u hu
    rwa [pow_two] at this
  have h3 : ∀ x ∈ conjClosure S.V3 H, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x := fun x _ => by
    have e : c * c * c = 1 := by rw [← pow_three', hc3]
    calc c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
      _ = x := by rw [e]; group

  set Gen : Set G := {w | ∃ l ∈ S.L1, ∃ u ∈ conjClosure S.V3 H,
    (∀ o ∈ pCoreOf 2 S.L1, o * u * o⁻¹ * u⁻¹ ∈ fsuV1 T V) ∧ l * u * l⁻¹ * u⁻¹ = w} with hGen

  obtain ⟨P, hP⟩ := A6L74.exists_tr3Pre hUab hcU (fsuV1 T V)
  have htrV : ∀ v ∈ fsuV1 T V, A6L74.tr3 c v = v := fun v hv => by
    unfold A6L74.tr3
    have e : c * c * v * c⁻¹ * c⁻¹ = c * (c * v * c⁻¹) * c⁻¹ := by group
    rw [e, hV1c v hv c hcH, hV1c v hv c hcH, hsq v (hV1U hv), one_mul]
  have hgen : ∀ (j : ℕ) (o : G), o ∈ pCoreOf 2 S.L1 → ∀ u ∈ conjClosure S.V3 H,
      (∀ o' ∈ pCoreOf 2 S.L1, o' * u * o'⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      A6L74.tr3 c ((c ^ j * o) * u * (c ^ j * o)⁻¹ * u⁻¹) ∈ fsuV1 T V := by
    intro j o ho u hu hou
    have hv := hou o ho
    have hcj : c ^ j ∈ H := H.pow_mem hcH j
    have e : (c ^ j * o) * u * (c ^ j * o)⁻¹ * u⁻¹ =
        (c ^ j * (o * u * o⁻¹ * u⁻¹) * (c ^ j)⁻¹) * (c ^ j * u * (c ^ j)⁻¹ * u⁻¹) := by group
    have hcjU : c ^ j * u * (c ^ j)⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hHU hcj) u).mp hu
    rw [e, hV1c _ hv _ hcj, A6L74.tr3_mul hUab hcU (hV1U hv)
      ((conjClosure S.V3 H).mul_mem hcjU ((conjClosure S.V3 H).inv_mem hu)),
      A6L74.tr3_comm_pow hUab hcU h3 hu j, mul_one, htrV _ hv]
    exact hv
  have hUP : Subgroup.closure Gen ⊔ fsuV1 T V ≤ P := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) fun v hv =>
      (hP v).2 ⟨hV1U hv, by rw [htrV v hv]; exact hv⟩
    rintro _ ⟨l, hl, u, hu, hou, rfl⟩
    have hlU : l * u * l⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hL1H hl)) u).mp hu
    refine (hP _).2 ⟨(conjClosure S.V3 H).mul_mem hlU ((conjClosure S.V3 H).inv_mem hu), ?_⟩
    have e3 : c * c * c = 1 := by rw [← pow_three', hc3]
    rcases S.L1_decomp hhat hl with h | h | h
    · have e : l = c ^ 0 * l := by simp
      rw [e]
      exact hgen 0 l h u hu hou
    · have e : l = c ^ 1 * (c * c * l) := by
        rw [pow_one]
        calc l = (c * c * c) * l := by rw [e3, one_mul]
          _ = c * (c * c * l) := by group
      rw [e]
      exact hgen 1 _ h u hu hou
    · have e : l = c ^ 2 * (c * l) := by
        rw [pow_two]
        calc l = (c * c * c) * l := by rw [e3, one_mul]
          _ = c * c * (c * l) := by group
      rw [e]
      exact hgen 2 _ h u hu hou
  refine ⟨Subgroup.closure Gen ⊔ fsuV1 T V, ?_, le_sup_right, ?_, ?_, ?_⟩
  ·
    refine sup_le ((Subgroup.closure_le _).2 ?_) hV1U
    rintro _ ⟨l, hl, u, hu, -, rfl⟩
    exact (conjClosure S.V3 H).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hHU (hL1H hl)) u).mp hu) ((conjClosure S.V3 H).inv_mem hu)
  ·
    intro v hv
    have hcV : c ∈ Subgroup.normalizer (S.V3 : Set G) :=
      S.L1T_le_NV3 (Subgroup.mem_sup_left hcL)
    obtain ⟨v₁, hv₁⟩ : ∃ v₁, v₁ = c * v * c⁻¹ := ⟨_, rfl⟩
    obtain ⟨v₂, hv₂⟩ : ∃ v₂, v₂ = c * v₁ * c⁻¹ := ⟨_, rfl⟩
    have hv₁V : v₁ ∈ S.V3 := hv₁ ▸ (Subgroup.mem_normalizer_iff.mp hcV v).mp hv
    have hv₂V : v₂ ∈ S.V3 := hv₂ ▸ (Subgroup.mem_normalizer_iff.mp hcV v₁).mp hv₁V
    have hcv₂ : c * v₂ * c⁻¹ = v := by
      rw [hv₂, hv₁]
      have e : c * c * c = 1 := by rw [← pow_three', hc3]
      calc c * (c * (c * v * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * v * (c * c * c)⁻¹ := by group
        _ = v := by rw [e]; group
    obtain ⟨N, hNdef⟩ : ∃ N, N = v * v₁ * v₂ := ⟨_, rfl⟩
    have hNV : N ∈ S.V3 := hNdef ▸ S.V3.mul_mem (S.V3.mul_mem hv hv₁V) hv₂V
    have hab3 : ∀ x ∈ S.V3, ∀ y ∈ S.V3, x * y = y * x := fun x hx y hy =>
      hUab x (le_conjClosure S.V3 H hx) y (le_conjClosure S.V3 H hy)
    have hcN : c * N * c⁻¹ = N := by
      rw [hNdef]
      calc c * (v * v₁ * v₂) * c⁻¹ = (c * v * c⁻¹) * (c * v₁ * c⁻¹) * (c * v₂ * c⁻¹) := by group
        _ = v₁ * v₂ * v := by rw [← hv₁, ← hv₂, hcv₂]
        _ = v * v₁ * v₂ := by
          rw [hab3 _ (S.V3.mul_mem hv₁V hv₂V) v hv, mul_assoc]
    have hNV1 : N ∈ fsuV1 T V := by
      refine mem_V1_of_c012 (S.cL1_rho hhat) hNV ?_
      rw [← hcdef, hcN, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hsq1 : v₁ * v₁ = 1 := hsq v₁ (le_conjClosure S.V3 H hv₁V)
    obtain ⟨a, hadef⟩ : ∃ a, a = c * v₁ * c⁻¹ * v₁⁻¹ := ⟨_, rfl⟩
    have hvNa : v = N * a⁻¹ := by
      rw [hNdef, hadef, ← hv₂]
      calc v = v * (v₁ * v₁) := by rw [hsq1, mul_one]
        _ = v * v₁ * (v₂ * v₁ * v₂⁻¹) := by
          rw [mul_assoc, hab3 v₂ hv₂V v₁ hv₁V]; group
        _ = v * v₁ * v₂ * (v₂ * v₁⁻¹)⁻¹ := by group
    rw [hvNa]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hNV1)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ?_)))
    exact ⟨c, hcL, v₁, le_conjClosure S.V3 H hv₁V, fun o ho => S.comm_O2L1_V3 ho hv₁V,
      hadef.symm⟩
  ·
    intro g hg hgL
    have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 S.L1 hgL
    refine A6L19.mem_normalizer_of_conj fun y hy => ?_
    have hle : Subgroup.closure Gen ⊔ fsuV1 T V ≤
        (Subgroup.closure Gen ⊔ fsuV1 T V).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
      · rintro _ ⟨l, hl, u, hu, hou, rfl⟩
        show g * (l * u * l⁻¹ * u⁻¹) * g⁻¹ ∈ Subgroup.closure Gen ⊔ fsuV1 T V
        refine Subgroup.mem_sup_left (Subgroup.subset_closure ⟨g * l * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgL l).mp hl, g * u * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hHU hg) u).mp hu, fun o ho => ?_, by group⟩)
        have ho' : g⁻¹ * o * g ∈ pCoreOf 2 S.L1 := by
          have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgO) o).mp ho
          simpa using this
        have h1 := hou _ ho'
        have e : o * (g * u * g⁻¹) * o⁻¹ * (g * u * g⁻¹)⁻¹ =
            g * ((g⁻¹ * o * g) * u * (g⁻¹ * o * g)⁻¹ * u⁻¹) * g⁻¹ := by group
        rw [e, hV1c _ h1 g hg]
        exact h1
      · intro v hv
        show g * v * g⁻¹ ∈ Subgroup.closure Gen ⊔ fsuV1 T V
        rw [hV1c v hv g hg]
        exact Subgroup.mem_sup_right hv
    exact hle hy
  ·
    intro u hu hcu
    have huU : u ∈ conjClosure S.V3 H := ((hP u).1 (hUP hu)).1
    have htr : A6L74.tr3 c u ∈ fsuV1 T V := ((hP u).1 (hUP hu)).2
    set v := c * u * c⁻¹ * u⁻¹ with hvdef
    have hvU : v ∈ conjClosure S.V3 H := hV1U hcu
    have hcuv : c * u * c⁻¹ = u * v := by
      rw [← hUab v hvU u huU, hvdef]
      group
    have heq := A6L74.eq_mul_of_tr3 (hsq u huU) (hsq v hvU) hcuv (hV1c v hcu c hcH)
      (hUab u huU v hvU)
    have e : u = A6L74.tr3 c u * v⁻¹ := by rw [heq]; group
    rw [e]
    exact (fsuV1 T V).mul_mem htr ((fsuV1 T V).inv_mem hcu)

end U1

section W

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G}
  (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)
include hNS h13315 h1356two hH hab hKH hHK hKL1

theorem exists_W_F4 (hhat : ¬ IsHatA6 L) (hK2 : oTwoRes K = K)
    (hKC : ∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
      k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3) :
    ∃ W : Subgroup G,
      W ≤ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧ W ≠ ⊥ ∧
      (∀ g ∈ H, g ∈ Subgroup.normalizer (S.L1 : Set G) →
        g ∈ Subgroup.normalizer (K : Set G) → g ∈ Subgroup.normalizer (W : Set G)) ∧
      (∀ w ∈ W, (∀ k ∈ K, k * w * k⁻¹ = w) → w = 1) ∧
      ∀ w ∈ W, (S.cL1 hhat : G) * w * (S.cL1 hhat : G)⁻¹ = w → w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hexp, -⟩ := A6L74.exp_comm_of_card_three h3
  obtain ⟨U₁, hU₁U, -, hV3U₁, hU₁N, hfpf⟩ := exists_U1_F4 hNS h13315 h1356two hH hab hhat
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hKL := K_le_normalizer_L1 hH hKH hHK hKL1
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := fun k hk => hU₁N k (hKH hk) (hKL hk)
  have hKU₀ : K ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    hKH.trans S.le_normalizer_U0
  have hHUH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hsq : ∀ u ∈ conjClosure S.V3 H, u * u = 1 := fun u hu => by
    have := hab.2 u hu
    rwa [pow_two] at this
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)

  have hMU₀ : ⁅U₁, K⁆ ≤ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      ⟨(conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHUH (hKH hk)) u).mp
        (hU₁U hu)) ((conjClosure S.V3 H).inv_mem (hU₁U hu)), hKC k hk u (hU₁U hu)⟩
    have e : ⁅u, k⁆ = (k * u * k⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hMU₁ : ⁅U₁, K⁆ ≤ U₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hKU₁
  have hKM' : K ≤ Subgroup.normalizer ((⁅U₁, K⁆ : Subgroup G) : Set G) := fun k hk =>
    SBd5.mem_normalizer_commutator_of (hKU₁ hk) (Subgroup.le_normalizer hk)
  have hWM : ⁅⁅U₁, K⁆, K⁆ ≤ ⁅U₁, K⁆ := Subgroup.le_normalizer_iff_commutator_le_left.mp hKM'

  have hOC : ∀ o ∈ pCoreOf 2 K, ∀ x ∈ conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G), o * x * o⁻¹ = x := fun o ho x hx => by
    rw [Subgroup.mem_centralizer_iff.mp hx.2 o (hOQ ho)]
    group

  obtain ⟨k₀, hk₀, hk₀O⟩ := A6L74.exists_not_mem_pCoreOf_of_card_three h3

  have hU₀ab : ∀ x ∈ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G),
      ∀ y ∈ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
  have hk₀U := hKU₀ hk₀
  have h3k : ∀ x ∈ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G),
      k₀ * k₀ * k₀ * x * k₀⁻¹ * k₀⁻¹ * k₀⁻¹ = x := fun x hx => by
    have h := hOC _ (hexp k₀ hk₀) x hx
    calc k₀ * k₀ * k₀ * x * k₀⁻¹ * k₀⁻¹ * k₀⁻¹ = k₀ ^ 3 * x * (k₀ ^ 3)⁻¹ := by
          rw [pow_three']
          simp only [mul_inv_rev, mul_assoc]
      _ = x := h
  obtain ⟨P', hP'⟩ := A6L74.exists_tr3Pre hU₀ab hk₀U (⊥ : Subgroup G)
  have hWP : ⁅⁅U₁, K⁆, K⁆ ≤ P' := by
    rw [Subgroup.commutator_le]
    intro m hm g hg
    obtain ⟨i, hi⟩ := A6L74.exists_pow_of_card_three h3 hk₀ hk₀O hg
    have hmU := hMU₀ hm
    have hgm : g * m⁻¹ * g⁻¹ = k₀ ^ i * m⁻¹ * (k₀ ^ i)⁻¹ := by
      have h1 := hOC _ hi m⁻¹ (Subgroup.inv_mem _ hmU)
      calc g * m⁻¹ * g⁻¹ = k₀ ^ i * (((k₀ ^ i)⁻¹ * g) * m⁻¹ * ((k₀ ^ i)⁻¹ * g)⁻¹) *
            (k₀ ^ i)⁻¹ := by group
        _ = k₀ ^ i * m⁻¹ * (k₀ ^ i)⁻¹ := by rw [h1]
    have hcm : k₀ ^ i * m⁻¹ * (k₀ ^ i)⁻¹ ∈ conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).pow_mem hk₀U i) _).mp
        (Subgroup.inv_mem _ hmU)
    have e : ⁅m, g⁆ = m * (g * m⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    refine (hP' _).2 ⟨?_, ?_⟩
    · rw [e, hgm]
      exact Subgroup.mul_mem _ hmU hcm
    · rw [e, hgm, A6L74.tr3_mul hU₀ab hk₀U hmU hcm,
        A6L74.tr3_conj_pow hU₀ab hk₀U h3k (Subgroup.inv_mem _ hmU) i,
        A6L74.tr3_inv hU₀ab hk₀U hmU, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hKfix : ∀ w ∈ ⁅⁅U₁, K⁆, K⁆, (∀ k ∈ K, k * w * k⁻¹ = w) → w = 1 := by
    intro w hw hwK
    have h1 := ((hP' w).1 (hWP hw)).2
    rw [Subgroup.mem_bot] at h1
    have hwU := hMU₀ (hWM hw)
    have h2 : A6L74.tr3 k₀ w = w := by
      unfold A6L74.tr3
      have e : k₀ * k₀ * w * k₀⁻¹ * k₀⁻¹ = k₀ * (k₀ * w * k₀⁻¹) * k₀⁻¹ := by group
      rw [e, hwK k₀ hk₀, hwK k₀ hk₀, hsq w hwU.1, one_mul]
    rw [h2] at h1
    exact h1
  have hcfix : ∀ w ∈ ⁅⁅U₁, K⁆, K⁆, (S.cL1 hhat : G) * w * (S.cL1 hhat : G)⁻¹ = w → w = 1 := by
    intro w hw hcw
    have h1 : (S.cL1 hhat : G) * w * (S.cL1 hhat : G)⁻¹ * w⁻¹ ∈ fsuV1 T V := by
      rw [hcw, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hwV1 : w ∈ fsuV1 T V := hfpf w (hMU₁ (hWM hw)) h1
    exact hKfix w hw fun k hk => hF.conj_eq_of_mem_V₁ (hKH hk) hwV1

  have hW1 : ⁅⁅U₁, K⁆, K⁆ ≠ ⊥ := by
    intro hWbot
    apply hKM
    have hkV : ∀ k ∈ K, ∀ v ∈ S.V3, k * v * k⁻¹ * v⁻¹ ∈ fsuV1 T V := by
      intro k hk v hv
      have hvU₁ := hV3U₁ hv
      have hvU := hU₁U hvU₁
      obtain ⟨a, hadef⟩ : ∃ a, a = k * v * k⁻¹ * v⁻¹ := ⟨_, rfl⟩
      have haM : a ∈ ⁅U₁, K⁆ := by
        have h1 : ⁅v, k⁆ ∈ ⁅U₁, K⁆ := Subgroup.commutator_mem_commutator hvU₁ hk
        have e : a = ⁅v, k⁆⁻¹ := by rw [hadef, commutatorElement_def]; group
        rw [e]
        exact Subgroup.inv_mem _ h1
      have hka : k * a * k⁻¹ = a := by
        have h1 : ⁅a, k⁆ ∈ ⁅⁅U₁, K⁆, K⁆ := Subgroup.commutator_mem_commutator haM hk
        rw [hWbot, Subgroup.mem_bot, commutatorElement_def] at h1
        calc k * a * k⁻¹ = (a * k * a⁻¹ * k⁻¹)⁻¹ * a := by group
          _ = a := by rw [h1, inv_one, one_mul]
      have ha2 := hsq _ (hMU₀ haM).1
      have hkv : k * v * k⁻¹ = a * v := by rw [hadef]; group
      have hk2 : k * k * v * k⁻¹ * k⁻¹ = v := by
        calc k * k * v * k⁻¹ * k⁻¹ = k * (k * v * k⁻¹) * k⁻¹ := by
              simp only [mul_assoc]
          _ = k * (a * v) * k⁻¹ := by rw [hkv]
          _ = (k * a * k⁻¹) * (k * v * k⁻¹) := by group
          _ = v := by rw [hka, hkv, ← mul_assoc, ha2, one_mul]
      have h1 := hF.commutator_mem_V₁ (hOQ (hexp k hk)) hvU
      have e : k * v * k⁻¹ * v⁻¹ = k ^ 3 * v * (k ^ 3)⁻¹ * v⁻¹ := by
        have e1 : k ^ 3 * v * (k ^ 3)⁻¹ = k * (k * k * v * k⁻¹ * k⁻¹) * k⁻¹ := by
          rw [pow_three']
          simp only [mul_inv_rev, mul_assoc]
        rw [e1, hk2]
      rw [e]
      exact h1

    have hKV : K ≤ Subgroup.centralizer (S.V3 : Set G) := by
      rw [← hK2]
      refine (Subgroup.closure_le _).2 ?_
      rintro k ⟨hk, m, hm, hkm⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := A6L74.conj_eq_of_odd hF.elemAbelian_Vp (S.V1_le_V2.trans S.V2_le_V3)
        (fun w hw => hF.conj_eq_of_mem_V₁ (hKH hk) hw) (hkV k hk) hm hkm hv
      calc v * k = k * v * k⁻¹ * k := by rw [h1]
        _ = k * v := by group
    exact hKV.trans ((S.centralizer_V3_le_F4 h13315).trans S.NV_le_M)
  refine ⟨⁅⁅U₁, K⁆, K⁆, hWM.trans hMU₀, hW1, fun g hg hgL hgK => ?_, hKfix, hcfix⟩
  exact SBd5.mem_normalizer_commutator_of
    (SBd5.mem_normalizer_commutator_of (hU₁N g hg hgL) hgK) hgK

end W

end Setting4

end CFSG.Quasithin.H13.A6
