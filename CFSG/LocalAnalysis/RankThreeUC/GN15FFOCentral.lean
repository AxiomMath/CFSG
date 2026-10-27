module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOSwap
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutNormal
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOffender
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO

open CFSG.RankThree.FFModules
open scoped commutatorElement

section Central

variable {G : Type} [Group G]

private theorem elem_sq_eq_one {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A) {g : G}
    (hg : g ∈ A) : g * g = 1 := by
  have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) g hg
  rwa [pow_two] at this

private theorem elem_mul_comm {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A) {g h : G}
    (hg : g ∈ A) (hh : h ∈ A) : g * h = h * g := by
  have := hAel.toIsMulCommutative.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩
  exact congrArg Subtype.val this

private theorem central_gen {A : Subgroup G} {z a : G} (hz2 : z * z ≠ 1) (ha : a ∈ A)
    (hinv : a * z * a⁻¹ = z⁻¹)
    (hAz : ∀ b ∈ A, b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z⁻¹) :
    a ∉ A ⊓ Subgroup.centralizer ({z} : Set G) ∧
      A ≤ (A ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ Subgroup.zpowers a := by
  have hmem : ∀ b : G, b ∈ A ⊓ Subgroup.centralizer ({z} : Set G) ↔ b ∈ A ∧ b * z = z * b := by
    intro b
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact and_congr_right fun _ => eq_comm
  have h1 : a * z = z⁻¹ * a := by
    have := congrArg (· * a) hinv
    simpa [mul_assoc] using this
  refine ⟨fun h => ?_, fun b hb => ?_⟩
  · have hc := ((hmem a).1 h).2
    rw [h1] at hc
    have h2 : z⁻¹ = z := mul_right_cancel hc
    apply hz2
    calc z * z = z⁻¹ * z := by rw [h2]
      _ = 1 := inv_mul_cancel z
  · rcases hAz b hb with h | h
    · have hbz : b * z = z * b := by
        have := congrArg (· * b) h
        simpa [mul_assoc] using this
      exact Subgroup.mem_sup_left ((hmem b).2 ⟨hb, hbz⟩)
    · have h5 : b * z = z⁻¹ * b := by
        have := congrArg (· * b) h
        simpa [mul_assoc] using this
      have h6 : a * z⁻¹ = z * a := by
        have h3 := congrArg Inv.inv hinv
        have h4 : a * z⁻¹ * a⁻¹ = z := by simpa [mul_assoc] using h3
        have := congrArg (· * a) h4
        simpa [mul_assoc] using this
      have hab : (a * b) * z = z * (a * b) := by
        calc a * b * z = a * (b * z) := by rw [mul_assoc]
          _ = a * (z⁻¹ * b) := by rw [h5]
          _ = (a * z⁻¹) * b := by rw [mul_assoc]
          _ = (z * a) * b := by rw [h6]
          _ = z * (a * b) := by rw [mul_assoc]
      have h1' : a⁻¹ ∈ (A ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ Subgroup.zpowers a :=
        Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
      have h2' : a * b ∈ (A ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ Subgroup.zpowers a :=
        Subgroup.mem_sup_left ((hmem _).2 ⟨A.mul_mem ha hb, hab⟩)
      have hb' : b = a⁻¹ * (a * b) := by group
      rw [hb']
      exact Subgroup.mul_mem _ h1' h2'

end Central

section Three

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
  {ρ : Representation (ZMod 2) G W}

omit [Finite W] in
private theorem comm_on_cyclic {Z T T' : W →ₗ[ZMod 2] W} (hZ3 : ∀ w, Z (Z (Z w)) = w)
    (hTZ : ∀ w, T (Z w) = Z (T w)) (hT'Z : ∀ w, T' (Z w) = Z (T' w))
    {J : Submodule (ZMod 2) W} {s : W} (hJ : J = Submodule.span (ZMod 2) {s, Z (Z s)})
    (hZJ : ∀ w ∈ J, Z w ∈ J) (hTJ : ∀ w ∈ J, T w ∈ J) (hT'J : ∀ w ∈ J, T' w ∈ J) :
    ∀ w ∈ J, T (T' w) = T' (T w) := by
  have hsJ : s ∈ J := hJ ▸ Submodule.subset_span (by simp)
  have hZsJ : Z (Z s) ∈ J := hJ ▸ Submodule.subset_span (by simp)
  let K : Submodule (ZMod 2) W := J ⊓ LinearMap.ker (T * T' - T' * T)
  have hK : ∀ w, w ∈ K ↔ w ∈ J ∧ T (T' w) = T' (T w) := fun w => by
    simp only [K, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply,
      sub_eq_zero]
  have hsK : s ∈ K := by
    rw [hK]
    refine ⟨hsJ, ?_⟩
    obtain ⟨α, β, hTs⟩ := Submodule.mem_span_pair.1 (hJ ▸ hTJ s hsJ)
    obtain ⟨α', β', hT's⟩ := Submodule.mem_span_pair.1 (hJ ▸ hT'J s hsJ)
    rw [← hTs, ← hT's]
    simp only [map_add, map_smul, hTZ, hT'Z]
    rw [← hTs, ← hT's]
    simp only [map_add, map_smul, hZ3]
    module
  have hZK : ∀ w ∈ K, Z w ∈ K := by
    intro w hw
    rw [hK] at hw ⊢
    exact ⟨hZJ w hw.1, by rw [hTZ, hT'Z, hT'Z, hTZ, hw.2]⟩
  have hspan : J ≤ K := by
    rw [hJ, Submodule.span_le]
    intro w hw
    rcases hw with rfl | hw
    · exact hsK
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hZK _ (hZK _ hsK)
  intro w hw
  exact ((hK w).1 (hspan hw)).2


theorem false_of_inverts_central_three [Finite G] (hρ : Function.Injective ρ)
    {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hAb : IsBestOffender ρ A)
    {z a : G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (ha : a ∈ A) (hinv : a * z * a⁻¹ = z⁻¹)
    (hAz : ∀ b ∈ A, b * z * b⁻¹ = z ∨ b * z * b⁻¹ = z⁻¹)
    {L : Subgroup G} (hL : Group.IsPerfect ↥L) (hzL : z ∈ L)
    (hLz : ∀ l ∈ L, l * z = z * l) : False := by
  classical
  have hxx : ∀ x : W, x + x = 0 := fun x => by
    nth_rewrite 2 [← ZModModule.neg_eq_self x]; exact add_neg_cancel x
  have hxy : ∀ x y : W, x + y = 0 → x = y := fun x y h => by
    have := eq_neg_of_add_eq_zero_left h
    rwa [ZModModule.neg_eq_self] at this
  have h2 : ∀ x : W, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hxx x
  set A₀ : Subgroup G := A ⊓ Subgroup.centralizer {z} with hA₀def
  have hA₀A : A₀ ≤ A := inf_le_left
  have hmemA₀ : ∀ b : G, b ∈ A₀ ↔ b ∈ A ∧ b * z = z * b := by
    intro b
    rw [hA₀def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact and_congr_right fun _ => eq_comm
  have hz2 : z * z ≠ 1 := by
    intro h
    apply hz1
    calc z = z * (z * z) := by rw [h, mul_one]
      _ = 1 := by rw [← mul_assoc, ← pow_two, ← pow_succ]; exact hz3
  obtain ⟨haA₀, hgen⟩ := central_gen hz2 ha hinv hAz
  set Z : W →ₗ[ZMod 2] W := ρ z with hZdef
  have hz3' : z * z * z = 1 := by rw [← pow_three']; exact hz3
  have hZ3 : ∀ w, Z (Z (Z w)) = w := fun w => by
    have : ρ (z * z * z) w = w := by rw [hz3', map_one]; rfl
    simpa [map_mul, Module.End.mul_apply] using this
  have hZinj : Function.Injective Z := fun x y h => by
    have h' : Z (Z (Z x)) = Z (Z (Z y)) := by rw [h]
    rwa [hZ3, hZ3] at h'
  have hZne : ∃ w, Z w ≠ w := by
    by_contra hcon
    push Not at hcon
    apply hz1
    apply hρ
    rw [map_one]
    exact LinearMap.ext hcon
  have hsq : a * a = 1 := elem_sq_eq_one hAel ha
  have hss : ∀ w, ρ a (ρ a w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, hsq, map_one]; rfl
  have hZa : ∀ w, ρ a (Z w) = Z (Z (ρ a w)) := fun w => by
    have h1 : a * z = z * z * a := by
      have h3 : z⁻¹ = z * z := by rw [inv_eq_iff_mul_eq_one, ← mul_assoc]; exact hz3'
      have h4 : a * z = z⁻¹ * a := by rw [← hinv]; group
      rw [h4, h3]
    calc ρ a (Z w) = ρ (a * z) w := by rw [map_mul]; rfl
      _ = ρ (z * z * a) w := by rw [h1]
      _ = Z (Z (ρ a w)) := by simp [map_mul, Module.End.mul_apply, hZdef]
  have hZa2 : ∀ w, ρ a (Z (Z w)) = Z (ρ a w) := fun w => by
    rw [hZa, hZa, hZ3]
  have hcomm_b : ∀ b ∈ A₀, ∀ w, ρ b (Z w) = Z (ρ b w) := fun b hb w => by
    have hbz : b * z = z * b := ((hmemA₀ b).1 hb).2
    show ρ b (ρ z w) = ρ z (ρ b w)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hbz]
  have hcomm_ba : ∀ b ∈ A₀, ∀ w, ρ b (ρ a w) = ρ a (ρ b w) := fun b hb w => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      elem_mul_comm hAel (hA₀A hb) ha]
  have hcomm_L : ∀ l ∈ L, ∀ w, ρ l (Z w) = Z (ρ l w) := fun l hl w => by
    show ρ l (ρ z w) = ρ z (ρ l w)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hLz l hl]
  set J : Submodule (ZMod 2) W := LinearMap.ker (1 + Z + Z * Z) with hJdef
  have hmemJ : ∀ w, w ∈ J ↔ w + Z w + Z (Z w) = 0 := fun w => by
    simp [hJdef, LinearMap.mem_ker, LinearMap.add_apply, Module.End.mul_apply]
  have hJZ : ∀ w ∈ J, Z w ∈ J := fun w hw => by
    rw [hmemJ] at hw ⊢
    rw [hZ3]
    calc Z w + Z (Z w) + w = w + Z w + Z (Z w) := by abel
      _ = 0 := hw
  have hJa : ∀ w ∈ J, ρ a w ∈ J := fun w hw => by
    rw [hmemJ] at hw ⊢
    have h := congrArg (ρ a) hw
    rw [map_add, map_add, hZa, hZa2, map_zero] at h
    calc ρ a w + Z (ρ a w) + Z (Z (ρ a w)) = ρ a w + Z (Z (ρ a w)) + Z (ρ a w) := by abel
      _ = 0 := h
  have hJcomm : ∀ (T : W →ₗ[ZMod 2] W), (∀ w, T (Z w) = Z (T w)) → ∀ w ∈ J, T w ∈ J := by
    intro T hT w hw
    rw [hmemJ] at hw ⊢
    have h := congrArg T hw
    simp only [map_add, hT, map_zero] at h
    exact h
  have hJfix : ∀ w ∈ J, Z w = w → w = 0 := fun w hw hZw => by
    rw [hmemJ, hZw, hZw] at hw
    have : w + w + w = w := by rw [hxx w, zero_add]
    rwa [this] at hw
  obtain ⟨u₀, hu₀J, hu₀0⟩ : ∃ u ∈ J, u ≠ 0 := by
    obtain ⟨w, hw⟩ := hZne
    refine ⟨w + Z w, ?_, fun h => hw (hxy _ _ h).symm⟩
    rw [hmemJ]
    simp only [map_add, hZ3]
    calc w + Z w + (Z w + Z (Z w)) + (Z (Z w) + w)
        = (w + w) + (Z w + Z w) + (Z (Z w) + Z (Z w)) := by abel
      _ = 0 := by simp only [hxx]
  have hJb : ∀ b ∈ A₀, ∀ w ∈ J, ρ b w ∈ J := fun b hb w hw => hJcomm (ρ b) (hcomm_b b hb) w hw
  have hJL : ∀ l ∈ L, ∀ w ∈ J, ρ l w ∈ J := fun l hl w hw => hJcomm (ρ l) (hcomm_L l hl) w hw
  set S₀ : Submodule (ZMod 2) W := J ⊓ LinearMap.eqLocus (ρ a) LinearMap.id with hS₀def
  have hmemS₀ : ∀ w, w ∈ S₀ ↔ w ∈ J ∧ ρ a w = w := fun w => by
    simp [hS₀def, LinearMap.mem_eqLocus]
  set I : Submodule (ZMod 2) W := S₀.map Z with hIdef
  have hmemI : ∀ w, w ∈ I ↔ ∃ s ∈ S₀, Z s = w := fun w => Submodule.mem_map
  have hI : ∀ b ∈ A₀, ∀ u ∈ I, ρ b u ∈ I := by
    intro b hb u hu
    obtain ⟨s, hs, rfl⟩ := (hmemI u).1 hu
    obtain ⟨hsJ, hsa⟩ := (hmemS₀ s).1 hs
    refine (hmemI _).2 ⟨ρ b s, (hmemS₀ _).2 ⟨hJb b hb s hsJ, ?_⟩, (hcomm_b b hb s).symm⟩
    rw [← hcomm_ba b hb s, hsa]
  have hdisj : I ⊓ I.map (ρ a) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨s₁, hs₁, rfl⟩ := (hmemI w).1 hw1
    obtain ⟨u, hu, hua⟩ := Submodule.mem_map.1 hw2
    obtain ⟨s₂, hs₂, rfl⟩ := (hmemI u).1 hu
    obtain ⟨hs₁J, hs₁a⟩ := (hmemS₀ s₁).1 hs₁
    obtain ⟨hs₂J, hs₂a⟩ := (hmemS₀ s₂).1 hs₂
    rw [hZa, hs₂a] at hua
    have h1 : Z s₂ = s₁ := hZinj hua
    have h2' : s₁ = Z (Z s₂) := by rw [← hs₁a, ← h1, hZa, hs₂a]
    have h3 : s₂ = Z s₂ := hZinj (h1.trans h2')
    have h4 : s₂ = 0 := hJfix s₂ hs₂J h3.symm
    have h5 : s₁ = 0 := by rw [← h1, h4, map_zero]
    rw [h5, map_zero]
    exact Submodule.zero_mem _
  have hswap := card_le_two_of_swap hAel hAb hA₀A ha haA₀ hgen I hI (disjoint_iff.2 hdisj)
  have hS₀card : Nat.card S₀ ≤ 2 := by
    have := Nat.card_congr (Submodule.equivMapOfInjective Z hZinj S₀).toEquiv
    rw [hIdef] at hswap
    omega
  set M₂ : Submodule (ZMod 2) W := S₀.map (Z * Z) with hM₂def
  have hJle : J ≤ S₀ ⊔ M₂ := by
    intro u hu
    have hP : u + Z u + Z (Z u) = 0 := (hmemJ u).1 hu
    have hZu := hJZ u hu
    have ht : u + ρ a u ∈ S₀ :=
      (hmemS₀ _).2 ⟨J.add_mem hu (hJa u hu), by rw [map_add, hss, add_comm]⟩
    have ht' : Z u + ρ a (Z u) ∈ S₀ :=
      (hmemS₀ _).2 ⟨J.add_mem hZu (hJa _ hZu), by rw [map_add, hss, add_comm]⟩
    refine Submodule.mem_sup.2 ⟨Z u + ρ a (Z u), ht', (Z * Z) (u + ρ a u),
      Submodule.mem_map_of_mem ht, ?_⟩
    have e : Z u + Z (Z u) = u := hxy _ _ (by
      calc Z u + Z (Z u) + u = u + Z u + Z (Z u) := by abel
        _ = 0 := hP)
    simp only [Module.End.mul_apply, map_add, hZa]
    calc Z u + Z (Z (ρ a u)) + (Z (Z u) + Z (Z (ρ a u)))
        = (Z u + Z (Z u)) + (Z (Z (ρ a u)) + Z (Z (ρ a u))) := by abel
      _ = u := by rw [e, hxx, add_zero]
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h
    have hM : M₂ = ⊥ := by rw [hM₂def, h, Submodule.map_bot]
    have := hJle hu₀J
    rw [h, hM, sup_bot_eq] at this
    exact hu₀0 ((Submodule.mem_bot _).1 this)
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS₀ne
  have hfin1 : Module.finrank (ZMod 2) S₀ = 1 := by
    have hle : Module.finrank (ZMod 2) S₀ ≤ 1 := by
      have h := CFSG.RankThree.FFModules.card_eq_two_pow_finrank S₀
      by_contra hcon
      push Not at hcon
      have : 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) S₀ := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    have hpos : 0 < Module.finrank (ZMod 2) S₀ := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Submodule.finrank_eq_zero] at h
      exact hS₀ne h
    omega
  have hS₀span : ∀ t ∈ S₀, ∃ c : ZMod 2, c • s = t := by
    intro t ht
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨s, hsS⟩ : S₀)
      (fun h => hs0 (congrArg Subtype.val h))).1 hfin1 ⟨t, ht⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hsJ : s ∈ J := ((hmemS₀ s).1 hsS).1
  have hJspan : J = Submodule.span (ZMod 2) {s, Z (Z s)} := by
    apply le_antisymm
    · intro u hu
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.1 (hJle hu)
      obtain ⟨c₁, rfl⟩ := hS₀span t₁ ht₁
      obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht₂
      obtain ⟨c₂, rfl⟩ := hS₀span t' ht'
      refine Submodule.add_mem _ (Submodule.smul_mem _ c₁ (Submodule.subset_span (by simp))) ?_
      have : (Z * Z) (c₂ • s) = c₂ • Z (Z s) := by simp [Module.End.mul_apply]
      rw [this]
      exact Submodule.smul_mem _ c₂ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro w hw
      rcases hw with rfl | hw
      · exact hsJ
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hJZ _ (hJZ _ hsJ)
  have hcomm_on : ∀ g ∈ L, ∀ g' ∈ L, ∀ w ∈ J, ρ g (ρ g' w) = ρ g' (ρ g w) :=
    fun g hg g' hg' => comm_on_cyclic hZ3 (hcomm_L g hg) (hcomm_L g' hg') hJspan hJZ (hJL g hg)
      (hJL g' hg')
  have hρinv : ∀ (g : G) (w : W), ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hLL : ⁅L, L⁆ = L := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) L.subtype
    have h2 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
      have := hL.commutator_eq_top
      rwa [commutator_def] at this
    rw [h2] at h1
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h1.symm
  have hcen : ⁅L, L⁆ ≤ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.cenOn ρ L J := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hmem : ⁅g₁, g₂⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hg₁ hg₂) (L.inv_mem hg₁)) (L.inv_mem hg₂)
    refine ⟨hmem, fun w hw => ?_⟩
    have hw₁ : ρ g₂⁻¹ w ∈ J := hJL _ (L.inv_mem hg₂) w hw
    have hw₂ : ρ g₁⁻¹ (ρ g₂⁻¹ w) ∈ J := hJL _ (L.inv_mem hg₁) _ hw₁
    have hc := hcomm_on g₂ hg₂ g₁⁻¹ (L.inv_mem hg₁) (ρ g₂⁻¹ w) hw₁
    rw [commutatorElement_def]
    simp only [map_mul, Module.End.mul_apply]
    rw [hc, hρinv g₂ w, hρinv g₁ w]
  have hzfix : ∀ w ∈ J, Z w = w := fun w hw => by
    have := (hLL ▸ hcen) hzL
    exact this.2 w hw
  exact hu₀0 (hJfix u₀ hu₀J (hzfix u₀ hu₀J))


theorem false_of_inverts_central [Finite G] (hρ : Function.Injective ρ)
    {A : Subgroup G} (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hAb : IsBestOffender ρ A)
    {z a : G} (hz1 : z ≠ 1) (hzodd : Odd (orderOf z)) (ha : a ∈ A) (hinv : a * z * a⁻¹ = z⁻¹)
    (hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G))
    {L : Subgroup G} (hL : Group.IsPerfect ↥L) (hzL : z ∈ L)
    (hLz : ∀ l ∈ L, l * z = z * l) : False := by
  by_cases h3 : 3 ∣ orderOf z
  · obtain ⟨m, hm⟩ := h3
    set z' : G := z ^ m with hz'
    have hz'3 : z' ^ 3 = 1 := by
      rw [hz', ← pow_mul, mul_comm, ← hm]; exact pow_orderOf_eq_one z
    have hz'1 : z' ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      have hpos : 0 < orderOf z := orderOf_pos z
      rw [hm] at this
      have hm0 : 0 < m := by rcases Nat.eq_zero_or_pos m with h0 | h0 <;> [omega; exact h0]
      have := Nat.le_of_dvd hm0 this
      omega
    refine false_of_inverts_central_three hρ hAel hAb hz'3 hz'1 ha ?_ ?_ hL
      (L.pow_mem hzL m) (fun l hl => by
        have := hLz l hl
        rw [hz']; exact (Commute.pow_right (show Commute l z from this) m).eq)
    · rw [hz', ← conj_pow, hinv, inv_pow]
    · intro b hb
      have hbN : b * z * b⁻¹ ∈ Subgroup.zpowers z :=
        (Subgroup.mem_normalizer_iff.1 (hAN hb) z).1 (Subgroup.mem_zpowers z)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbN
      have hconj : b * z' * b⁻¹ = z' ^ k := by
        rw [hz', ← conj_pow, ← hk, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
          mul_comm]
      have hmod := zpow_eq_zpow_emod k (show z' ^ (3 : ℤ) = 1 by exact_mod_cast hz'3)
      have hz'2 : z' ^ (2 : ℤ) = z'⁻¹ := by
        rw [zpow_two]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hz'3)
      rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
      · exfalso
        apply hz'1
        rw [h0, zpow_zero] at hmod
        rw [hmod] at hconj
        have : b * z' = b := by
          have := congrArg (· * b) hconj
          simpa [mul_assoc] using this
        exact mul_left_cancel (this.trans (mul_one b).symm)
      · left
        rw [hconj, hmod, h1, zpow_one]
      · right
        rw [hconj, hmod, h2, hz'2]
  · exact hz1 (eq_one_of_inverted_of_normalizes hρ hAel hAb hzodd h3 hAN ha hinv)


theorem card_le_two_of_swapped_pair [Finite G] {A : Subgroup G}
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hAb : IsBestOffender ρ A) {a : G} (ha : a ∈ A)
    (M₁ : Submodule (ZMod 2) W) (hdisj : Disjoint M₁ (M₁.map (ρ a)))
    (hA : ∀ b ∈ A, M₁.map (ρ b) = M₁ ∨ M₁.map (ρ b) = M₁.map (ρ a)) : Nat.card M₁ ≤ 2 := by
  classical
  have hsq : a * a = 1 := elem_sq_eq_one hAel ha
  have hmap_mul : ∀ (b c : G) (N : Submodule (ZMod 2) W),
      N.map (ρ (b * c)) = (N.map (ρ c)).map (ρ b) := fun b c N => by
    rw [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hmap_one : ∀ N : Submodule (ZMod 2) W, N.map (ρ 1) = N := fun N => by
    rw [map_one]; exact Submodule.map_id N
  let A₀ : Subgroup G :=
    { carrier := {b | b ∈ A ∧ M₁.map (ρ b) = M₁}
      mul_mem' := fun {b c} hb hc => ⟨A.mul_mem hb.1 hc.1, by rw [hmap_mul, hc.2, hb.2]⟩
      one_mem' := ⟨A.one_mem, hmap_one M₁⟩
      inv_mem' := fun {b} hb => ⟨A.inv_mem hb.1, by
        have h := congrArg (fun N => N.map (ρ b⁻¹)) hb.2
        rw [← hmap_mul, inv_mul_cancel, hmap_one] at h
        exact h.symm⟩ }
  have hA₀A : A₀ ≤ A := fun b hb => hb.1
  by_cases haA₀ : a ∈ A₀
  · have h1 : M₁.map (ρ a) = M₁ := haA₀.2
    rw [h1] at hdisj
    have : M₁ = ⊥ := disjoint_self.1 hdisj
    rw [this]
    have : Nat.card (↥(⊥ : Submodule (ZMod 2) W)) = 1 := Nat.card_unique
    omega
  · have hgen : A ≤ A₀ ⊔ Subgroup.zpowers a := by
      intro b hb
      rcases hA b hb with h | h
      · exact Subgroup.mem_sup_left ⟨hb, h⟩
      · have hab : a * b ∈ A₀ := by
          refine ⟨A.mul_mem ha hb, ?_⟩
          rw [hmap_mul, h, ← hmap_mul, hsq, hmap_one]
        have h1 : a⁻¹ ∈ A₀ ⊔ Subgroup.zpowers a :=
          Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
        have h2 : a * b ∈ A₀ ⊔ Subgroup.zpowers a := Subgroup.mem_sup_left hab
        have hb' : b = a⁻¹ * (a * b) := by group
        rw [hb']
        exact Subgroup.mul_mem _ h1 h2
    exact card_le_two_of_swap hAel hAb hA₀A ha haA₀ hgen M₁
      (fun b hb w hw => by
        have : ρ b w ∈ M₁.map (ρ b) := Submodule.mem_map_of_mem hw
        rwa [hb.2] at this) hdisj

end Three

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO
