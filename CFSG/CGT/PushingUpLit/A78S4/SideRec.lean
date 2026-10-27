module

public import CFSG.CGT.PushingUpLit.A78S4.Cfg
public import CFSG.CGT.PushingUpLit.A78S4.H1

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e)

include P

theorem conj_Z {m : G} (hm : m ∈ Subgroup.normalizer (V : Set G)) {z : G} (hz : z ∈ Z) :
    m * z * m⁻¹ ∈ Z := by
  have hmL : m ∈ Subgroup.normalizer (L₁ : Set G) := P.nl₁ hm
  refine P.side₁.mem_Z_of_cent (conj_mem_of_mem_normalizer hm (P.side₁.Z_le_V hz))
    (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
  have hl' : m⁻¹ * l * m ∈ L₁ := by
    simpa using conj_mem_of_mem_normalizer (inv_mem hmL) hl
  have hzl := Subgroup.mem_centralizer_iff.1 (P.side₁.Z_cent hz) _ hl'
  calc l * (m * z * m⁻¹) = m * ((m⁻¹ * l * m) * z) * m⁻¹ := by group
    _ = m * (z * (m⁻¹ * l * m)) * m⁻¹ := by rw [hzl]
    _ = m * z * m⁻¹ * l := by group

theorem normalizer_V_le_Z :
    Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
  le_normalizer_of_conj fun _ hm _ hz => P.conj_Z hm hz

variable (hZ : Z ≠ ⊥)

include hZ

theorem trans : ∀ z ∈ Z, z ≠ 1 → ∀ z' ∈ Z, z' ≠ 1 →
    ∃ m ∈ Subgroup.normalizer (V : Set G), m * z * m⁻¹ = z' := by
  intro z hz hz1 z' hz' hz'1
  obtain ⟨D₂⟩ := P.side₂.nat
  obtain ⟨fr₂⟩ := P.side₂.exists_frame D₂
  have hc0 : ∀ y ∈ Z, y ≠ 1 → fr₂.c y ≠ 0 := by
    intro y hy hy1 h0
    apply hy1
    have h1 : fr₂.c y = fr₂.c 1 := by rw [h0, fr₂.c_one]
    exact P.zc_inj fr₂ hy Z.one_mem h1
  have ht : fr₂.c z' / fr₂.c z ≠ 0 := div_ne_zero (hc0 z' hz' hz'1) (hc0 z hz hz1)
  obtain ⟨y, hyL, -, hyV, -, hyN⟩ := fr₂.torus ht
  have hyM : y ∈ Subgroup.normalizer (V : Set G) := mem_normalizer_of_conj_le hyV
  refine ⟨y, hyM, P.zc_inj fr₂ (P.conj_Z hyM hz) hz' ?_⟩
  rw [(hyN z (P.Z_le_N' hz)).2]
  field_simp [hc0 z hz hz1]

theorem cent_of_cent₀
    (h0 : ∀ z ∈ Z, z ≠ 1 → (∀ t ∈ T, t * z * t⁻¹ = z) →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ∀ z ∈ Z, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZel : ElemAb2 Z := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V x (P.side₁.Z_le_V hx) y (P.side₁.Z_le_V hy)).eq,
      P.side₁.jst.sq_V x (P.side₁.Z_le_V hx)⟩
  obtain ⟨z₀, hz₀, hz₀1, hz₀T⟩ := exists_fixed_ne_one P.side₁.pT hZel hZ
    (fun t ht => cj_eq_of_mem_normalizer_set (P.side₁.T_le_Z ht))
  have hC₀ := h0 z₀ hz₀ hz₀1 hz₀T
  intro z hz hz1
  obtain ⟨m, hm, hmz⟩ := P.trans hZ z₀ hz₀ hz₀1 z hz hz1
  intro g hg
  have hg' : m⁻¹ * g * m ∈ Subgroup.centralizer ({z₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hmz] at hg
    calc m⁻¹ * g * m * z₀ = m⁻¹ * (g * (m * z₀ * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * z₀ * m⁻¹) * g) * m := by rw [hg]
      _ = z₀ * (m⁻¹ * g * m) := by group
  have h1 := hC₀ hg'
  have e1 : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e1]
  exact mul_mem (mul_mem hm h1) (inv_mem hm)

theorem ti_of_cent
    (hcent : ∀ z ∈ Z, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ∀ g : G, Z ⊓ cj g Z ≠ ⊥ → cj g Z = Z := by
  intro g hg
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z ⊓ cj g Z, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hg ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hz' : g⁻¹ * z * g ∈ Z := (mem_cj_iff g Z z).1 hz.2
  have hz'1 : g⁻¹ * z * g ≠ 1 := fun h1 => hz1 (by
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h1]; group)
  obtain ⟨m, hm, hmz⟩ := P.trans hZ _ hz' hz'1 z hz.1 hz1
  have hmg : m⁻¹ * g ∈ Subgroup.centralizer ({g⁻¹ * z * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : m * (g⁻¹ * z * g) * m⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hmz]; group
    calc m⁻¹ * g * (g⁻¹ * z * g) = m⁻¹ * (g * (g⁻¹ * z * g) * g⁻¹) * g := by group
      _ = m⁻¹ * (m * (g⁻¹ * z * g) * m⁻¹) * g := by rw [e1]
      _ = (g⁻¹ * z * g) * (m⁻¹ * g) := by group
  have h1 := hcent _ hz' hz'1 hmg
  have hgM : g ∈ Subgroup.normalizer (V : Set G) := by
    have e2 : g = m * (m⁻¹ * g) := by group
    rw [e2]
    exact mul_mem hm h1
  exact cj_eq_of_mem_normalizer_set (P.normalizer_V_le_Z hgM)

omit hZ in
theorem le_comm_sup : V ≤ ⁅V, L₁⁆ ⊔ Z := by
  obtain ⟨D⟩ := P.side₁.nat
  have hcomm : ∀ w ∈ V, ∀ l ∈ L₁, w * (l * w⁻¹ * l⁻¹) ∈ ⁅V, L₁⁆ := by
    intro w hw l hl
    have e1 : w * (l * w⁻¹ * l⁻¹) = ⁅w, l⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [e1]
    exact Subgroup.commutator_mem_commutator hw hl
  have h0 : ∀ x : GaloisField 2 e, ∃ g ∈ ⁅V, L₁⁆, g ∈ V ∧ D.κ g = ![x, 0] := by
    intro x
    obtain ⟨w, hw, hwx⟩ := D.κ_surj ![0, -x]
    obtain ⟨l, hl, hlu⟩ := D.ρ_surj (CFSG.SL2MinimalFaithful.unipotent 1)
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcomm w hw l hl,
      mul_mem hw (D.norm l hl _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw hl, hlu, hwx, CFSG.SL2MinimalFaithful.coe_unipotent]
    ext i
    fin_cases i <;> simp
  have h1 : ∀ y : GaloisField 2 e, ∃ g ∈ ⁅V, L₁⁆, g ∈ V ∧ D.κ g = ![0, y] := by
    intro y
    obtain ⟨w, hw, hwy⟩ := D.κ_surj ![-y, 0]
    let u : SpecialLinearGroup (Fin 2) (GaloisField 2 e) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩
    obtain ⟨l, hl, hlu⟩ := D.ρ_surj u
    refine ⟨w * (l * w⁻¹ * l⁻¹), hcomm w hw l hl,
      mul_mem hw (D.norm l hl _ (inv_mem hw)), ?_⟩
    rw [D.κ_comm hw hl, hlu, hwy]
    ext i
    fin_cases i <;> simp [u]
  intro v hv
  obtain ⟨g₀, hg₀C, hg₀V, hg₀⟩ := h0 (D.κ v 0)
  obtain ⟨g₁, hg₁C, hg₁V, hg₁⟩ := h1 (D.κ v 1)
  have hκ : D.κ v = D.κ (g₀ * g₁) := by
    rw [D.κ_mul g₀ hg₀V g₁ hg₁V, hg₀, hg₁]
    ext i
    fin_cases i <;> simp
  have hz := (D.κ_eq_iff hv (mul_mem hg₀V hg₁V)).1 hκ
  have e : v = (g₀ * g₁) * ((g₀ * g₁)⁻¹ * (v * (g₀ * g₁)⁻¹) * (g₀ * g₁)) := by group
  rw [e]
  refine mul_mem (Subgroup.mem_sup_left (mul_mem hg₀C hg₁C)) (Subgroup.mem_sup_right ?_)
  have hgV : (g₀ * g₁)⁻¹ ∈ V := inv_mem (mul_mem hg₀V hg₁V)
  have hc := (P.side₁.jst.abelian_V _ hgV _ (P.side₁.Z_le_V hz)).eq
  have e2 : (g₀ * g₁)⁻¹ * (v * (g₀ * g₁)⁻¹) * (g₀ * g₁) = v * (g₀ * g₁)⁻¹ := by
    calc (g₀ * g₁)⁻¹ * (v * (g₀ * g₁)⁻¹) * (g₀ * g₁) =
          ((g₀ * g₁)⁻¹ * (v * (g₀ * g₁)⁻¹)) * (g₀ * g₁) := rfl
      _ = ((v * (g₀ * g₁)⁻¹) * (g₀ * g₁)⁻¹) * (g₀ * g₁) := by rw [hc]
      _ = v * (g₀ * g₁)⁻¹ := by group
  rw [e2]
  exact hz

end S4Pair

section Cfg

variable {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}
  (cfg : A78Cfg G L₁ L₂ T e)
  (hZ : oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) ≠ ⊥)

include cfg hZ

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_oTwoIn_L :
    oTwoIn L₁ = oTwoIn (L₁ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL := cfg.s4_V_le hZ
  apply le_antisymm
  · refine CGT6.le_oTwoIn_of_normal ((oTwoIn_le L₁).trans le_sup_left) ?_ (isPGroup_oTwoIn _)
    refine sup_le (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoIn L₁)) ?_
    exact cfg.side₁.sylow.le.trans (normalizer_le_normalizer_oTwoIn L₁)
  · exact CGT6.le_oTwoIn_of_normal hVL (le_sup_left.trans cfg.hyg.sup₁) (isPGroup_oTwoIn _)

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_normalizer_L :
    Subgroup.normalizer (L₁ : Set G) =
      Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) := by
  refine le_antisymm ?_ cfg.hyg.nl₁
  rw [← cfg.s4_oTwoIn_L hZ]
  exact normalizer_le_normalizer_oTwoIn L₁

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_cent_z :
    ∀ z ∈ oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G), z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := cfg.s4Pair hZ
  refine P.cent_of_cent₀ hZ fun z₀ hz₀ hz₀1 hz₀T => ?_
  have hord : z₀ * z₀ = 1 := cfg.side₁.comm_V z₀ hz₀.1 z₀ hz₀.1 ▸
    (elemAb2_of_isElemAbelian cfg.side₁.elem z₀ hz₀.1 z₀ hz₀.1).2
  have hP2 : IsPGroup 2 (Subgroup.zpowers z₀) := by
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hord) hz₀1
  have hP1 : Subgroup.zpowers z₀ ≠ ⊥ := by
    intro h0
    apply hz₀1
    have : z₀ ∈ Subgroup.zpowers z₀ := Subgroup.mem_zpowers z₀
    rw [h0] at this
    exact this
  have hCN : Subgroup.centralizer ({z₀} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers z₀ : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_le fun t ht => ?_
    obtain ⟨k, rfl⟩ := ht
    have hc : Commute g z₀ := (Subgroup.mem_centralizer_singleton_iff.1 hg)
    have hck : g * z₀ ^ k * g⁻¹ = z₀ ^ k := by
      rw [(hc.zpow_right k).eq]
      group
    show g * z₀ ^ k * g⁻¹ ∈ Subgroup.zpowers z₀
    rw [hck]
    exact ⟨k, rfl⟩
  have hX : L₁ ⊔ T ≤ Subgroup.normalizer ((Subgroup.zpowers z₀ : Subgroup G) : Set G) := by
    refine sup_le (fun l hl => hCN ?_) (fun t ht => hCN ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hz₀.2 l hl)
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc t * z₀ = t * z₀ * t⁻¹ * t := by group
        _ = z₀ * t := by rw [hz₀T t ht]
  have hN := CFSG.RankThree.PartOne.Sec15Final.normalizer_le_of_forall_maximal hP1 hP2 hX
    (N := Subgroup.normalizer (L₁ : Set G)) fun M hM => by
      rw [cfg.side₁.unique] at hM
      exact (Set.mem_singleton_iff.mp hM).le
  rw [← cfg.s4_normalizer_L hZ]
  exact hCN.trans hN

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_normalizer_Z :
    Subgroup.normalizer
        ((oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) : Set G) =
      Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := cfg.s4Pair hZ
  refine le_antisymm ?_ P.normalizer_V_le_Z
  have hZ2 : IsPGroup 2 ↥(oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G)) :=
    (isPGroup_oTwoIn _).to_le inf_le_left
  have hN := CFSG.RankThree.PartOne.Sec15Final.normalizer_le_of_forall_maximal hZ hZ2
    cfg.side₁.sup_le_normalizer_Z (N := Subgroup.normalizer (L₁ : Set G)) fun M hM => by
      rw [cfg.side₁.unique] at hM
      exact (Set.mem_singleton_iff.mp hM).le
  rw [← cfg.s4_normalizer_L hZ]
  exact hN

omit hZ in
theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_O2_M :
    ∀ P : Subgroup G, P ≤ Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) →
      IsPGroup 2 P →
      (P.subgroupOf (Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G))).Normal →
      P ≤ oTwoIn (L₁ ⊔ T) := by
  intro P hPM hP2 hPn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).1 hPn
  obtain ⟨k, hk, hkP⟩ := exists_conj_le_of_isSylowOf cfg.hyg.sylow₁ hPM hP2
  have hPT : P ≤ T := by
    rw [cj_eq_of_mem_normalizer_set (hnorm hk)] at hkP
    exact hkP
  exact CGT6.le_oTwoIn_of_normal (hPT.trans le_sup_right) (cfg.hyg.sup₁.trans hnorm) hP2

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_cent_V :
    Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) ⊓
      Subgroup.centralizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) ≤ oTwoIn (L₁ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G) with hM
  have htl : CFSG.Assembly.IsTwoLocal M := ⟨oTwoIn (L₁ ⊔ T), cfg.hyg.V₁_ne, isPGroup_oTwoIn _, rfl⟩
  have hcore : CFSG.Open.pCoreOf 2 M = oTwoIn (L₁ ⊔ T) := by
    refine le_antisymm ?_ ?_
    · refine cfg.s4_O2_M _ (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ?_
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (isPGroup_oTwoIn _)
  have h1 : M ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M :=
    cfg.charTwo M htl
  rw [hcore] at h1
  exact h1

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.s4_perfect : ⁅L₁, L₁⁆ = L₁ := by
  classical
  have P := cfg.s4Pair hZ
  have hVL := cfg.s4_V_le hZ
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) ?_
  have hVC : oTwoIn (L₁ ⊔ T) ≤ ⁅L₁, L₁⁆ := by
    refine P.le_comm_sup.trans (sup_le (Subgroup.commutator_mono hVL le_rfl) ?_)
    exact (P.Z_le_comm hZ).trans (Subgroup.commutator_mono hVL P.side₁.W_le_L)
  obtain ⟨φ, ψ, hs, hk, -⟩ := cfg.side₁.nat
  have hF4 : ∃ s : Finset (GaloisField 2 e), s.card = 4 := by
    have : Fintype (GaloisField 2 e) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 e))) (n := 4) (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, P.side₁.card_F]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) P.side₁.two_le)
    exact ⟨t, ht⟩
  have hperf := (CFSG.LinearGroups.special_linear_dimension_two_perfect hF4).commutator_eq_top
  intro l hl
  have h1 : φ ⟨l, hl⟩ ∈ Subgroup.map φ (⁅(⊤ : Subgroup ↥L₁), (⊤ : Subgroup ↥L₁)⁆) := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hs]
    have : φ ⟨l, hl⟩ ∈ commutator (SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
      rw [hperf]; exact Subgroup.mem_top _
    rwa [commutator_def] at this
  obtain ⟨c, hc, hcl⟩ := h1
  have hker : (⟨l, hl⟩ : ↥L₁) * c⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcl, mul_inv_cancel]
  rw [hk, Subgroup.mem_subgroupOf] at hker
  have hlcV : l * (c : G)⁻¹ ∈ L₁ ⊓ oTwoIn (L₁ ⊔ T) := by
    rw [cfg.side₁.inf_V_eq_centralizer]
    exact hker
  have hcC : (c : G) ∈ ⁅L₁, L₁⁆ := by
    have h2 : (c : G) ∈ Subgroup.map L₁.subtype (⁅(⊤ : Subgroup ↥L₁), (⊤ : Subgroup ↥L₁)⁆) :=
      ⟨c, hc, rfl⟩
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact h2
  have e1 : l = (l * (c : G)⁻¹) * c := by group
  rw [e1]
  exact mul_mem (hVC hlcV.2) hcC

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.sp4Side :
    Sp4Side G L₁ (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₁ ⊔ T) ⊓ Subgroup.centralizer (L₁ : Set G))
      (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) T
      (Subgroup.normalizer ((oTwoIn (L₁ ⊔ T) : Subgroup G) : Set G)) e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := cfg.s4Pair hZ
  obtain ⟨D⟩ := P.side₁.nat
  have hcent := cfg.s4_cent_z hZ
  exact
    { V_le_L := P.side₁.V_le_L
      L_le_M := D.le_normalizer
      normal_L := (Subgroup.normal_subgroupOf_iff_le_normalizer D.le_normalizer).2 P.nl₁
      M_eq := rfl
      Z_eq := rfl
      J_le_L := P.side₁.J_le_L
      T_le_M := P.side₁.T_le_V
      sylow_T := cfg.hyg.sylow₁
      T_inf_L := P.side₁.sylowJ.eq_of_le (le_inf P.side₁.J_le_T P.side₁.J_le_L) inf_le_right
        (P.side₁.pT.to_le inf_le_left)
      perfect := cfg.s4_perfect hZ
      cent_V := cfg.s4_cent_V hZ
      O2_M := cfg.s4_O2_M
      card_Z := P.card_Z hZ
      cent_z := hcent
      normalizer_Z := cfg.s4_normalizer_Z hZ
      ti := P.ti_of_cent hZ hcent
      trans := P.trans hZ }

end Cfg

end CFSG.CGT.PushingUpLit.A78S4
