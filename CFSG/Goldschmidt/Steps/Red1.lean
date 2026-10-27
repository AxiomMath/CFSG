module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Components
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification

theorem N18 :
    ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G), A ≤ S →
      IsMulCommutative A → fusionStronglyClosed (A : Set G) (S : Subgroup G) →
      Subgroup.normalClosure (A : Set G) = ⊤ →
      A ⊓ CFSG.Open.pCore 2 G ≤ Subgroup.center G ∧
        ⁅CFSG.Open.pCore 2 G, A⁆ ≤ A ⊓ CFSG.Open.pCore 2 G := by
  intro G _ _ S A hAS hAab hcl htop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (CFSG.Open.pCore 2 G).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have hQS : CFSG.Open.pCore 2 G ≤ S :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).le_sylow_of_normal S
  set Q := CFSG.Open.pCore 2 G
  have hDn : (A ⊓ Q).Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hq : g * d * g⁻¹ ∈ Q := hQn.conj_mem d hd.2 g
    refine ⟨?_, hq⟩
    have h := hcl d hd.1 g⁻¹ (by simpa using hQS hq)
    simpa using h
  refine ⟨?_, ?_⟩
  ·
    have hAC : (A : Set G) ⊆ Subgroup.centralizer ((A ⊓ Q : Subgroup G) : Set G) := by
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro d hd
      exact congrArg Subtype.val (hAab.is_comm.comm ⟨d, hd.1⟩ ⟨a, ha⟩)
    have hle := Subgroup.normalClosure_le_normal hAC
    rw [htop] at hle
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) d hd).symm
  · rw [Subgroup.commutator_le]
    intro q hq a ha
    have h1 : q * a * q⁻¹ ∈ A := by
      simpa using conj_mem_of_stronglyClosed hAS hcl ((S : Subgroup G).inv_mem (hQS hq)) ha
    have h2 : a * q⁻¹ * a⁻¹ ∈ Q := hQn.conj_mem _ (Q.inv_mem hq) a
    rw [commutatorElement_def]
    exact ⟨A.mul_mem h1 (A.inv_mem ha), by simpa [mul_assoc] using Q.mul_mem hq h2⟩

private theorem isComponentOf_conjSub {G : Type*} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K ⊤) (g : G) : IsComponentOf (conjSub g K) ⊤ := by
  unfold conjSub
  exact (LocalComponents.equiv_iff (MulAut.conj g⁻¹) K).mpr hK

private theorem conjSub_component_eq {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {A : Subgroup G} (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set G) (S : Subgroup G)) {K : Subgroup G}
    (hK : IsComponentOf K ⊤) {a : G} (ha : a ∈ A) : conjSub a K = K := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := conjSub a K
  have hL : IsComponentOf L ⊤ := isComponentOf_conjSub hK a
  have hKL : K ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (N8b G K L hK hL (Ne.symm hne))
  have hcomm : ∀ c ∈ K, ∀ x ∈ K, c * (a⁻¹ * x * a) = (a⁻¹ * x * a) * c := fun c hc x hx =>
    (Subgroup.mem_centralizer_iff.mp (hKL hc) _ (conj_mem_conjSub hx)).symm
  have key : ∀ x ∈ (S : Subgroup G), x ∈ K → ∀ c ∈ K, c * x * c⁻¹ ∈ (S : Subgroup G) →
      x⁻¹ * (c * x * c⁻¹) ∈ A := by
    intro x hxS hxK c hcK hyS
    set w := a⁻¹ * x * a with hwdef
    have hwS : w ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hAS ha)) hxS) (hAS ha)
    have hcw : c * w⁻¹ = w⁻¹ * c := (Commute.inv_right (hcomm c hcK x hxK)).eq
    set y := w⁻¹ * x with hydef
    have hyA : y ∈ A := by
      have h : y = a⁻¹ * (x⁻¹ * a * x) := by rw [hydef, hwdef]; group
      rw [h]
      exact A.mul_mem (A.inv_mem ha) (conj_mem_of_stronglyClosed hAS hcl hxS ha)
    have hcy : c * y * c⁻¹ = w⁻¹ * (c * x * c⁻¹) := by
      calc c * y * c⁻¹ = c * w⁻¹ * x * c⁻¹ := by rw [hydef]; group
        _ = w⁻¹ * c * x * c⁻¹ := by rw [hcw]
        _ = w⁻¹ * (c * x * c⁻¹) := by group
    have hcyA : c * y * c⁻¹ ∈ A := by
      have h := hcl y hyA c⁻¹ (by
        rw [inv_inv, hcy]
        exact (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hwS) hyS)
      rwa [inv_inv] at h
    have h : x⁻¹ * (c * x * c⁻¹) = y⁻¹ * (c * y * c⁻¹) := by
      rw [hcy, hydef]; group
    rw [h]
    exact A.mul_mem (A.inv_mem hyA) hcyA
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (Components.mathlib_subnormal_of_chain hK.2.1 Subgroup.IsSubnormal.top)
  have hTmem : ∀ x : K, x ∈ (T : Subgroup K) → (x : G) ∈ (S : Subgroup G) := by
    intro x hx
    have h : (x : G) ∈ (T : Subgroup K).map K.subtype := ⟨x, hx, rfl⟩
    rw [hT] at h
    exact h.1
  have hperf : CFSG.derivedSubgroup K = ⊤ := hK.2.2.1
  have hfocal := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup 2 T
  rw [hperf, inf_top_eq] at hfocal
  have hTA : (T : Subgroup K) ≤ A.subgroupOf K := by
    rw [hfocal, Subgroup.closure_le]
    rintro z ⟨u, hu, v, hv, huv, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.mp huv
    have h := key u (hTmem u hu) u.2 c c.2 (by simpa using hTmem _ hv)
    simpa [Subgroup.mem_subgroupOf] using h
  have hTZ : (T : Subgroup K) ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro c
    have hxA : (x : G) ∈ A := hTA hx
    have hax : a * (x : G) = x * a := congrArg Subtype.val (hAab.is_comm.comm ⟨a, ha⟩ ⟨x, hxA⟩)
    have hxa : a⁻¹ * (x : G) * a = x := by
      rw [mul_assoc, ← hax, ← mul_assoc, inv_mul_cancel, one_mul]
    have h := hcomm c c.2 x x.2
    rw [hxa] at h
    exact Subtype.ext h
  have hodd : Odd (Nat.card (K ⧸ Subgroup.center K)) := by
    have h1 : (Subgroup.center K).index ∣ (T : Subgroup K).index := Subgroup.index_dvd_of_le hTZ
    show Odd (Subgroup.center K).index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => T.not_dvd_index (h.trans h1))
  have hsolv := CFSG.Milestones.odd_order_solvable hodd
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (K ⧸ Subgroup.center K) hsolv

theorem N19 : S_N19 := by
  intro G _ _ S A hAS hAab hcl htop K hK
  have hconj : ∀ g : G, ∀ a ∈ A, g * a * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
    intro g a ha
    have h1 : conjSub (g * a * g⁻¹) K = K := by
      rw [conjSub_mul, conjSub_mul,
        conjSub_component_eq S hAS hAab hcl (isComponentOf_conjSub hK g) ha, ← conjSub_mul,
        mul_inv_cancel, conjSub_one]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← mem_conjSub, h1]
  have hKn : K.Normal := by
    have hle : Subgroup.normalClosure (A : Set G) ≤ Subgroup.normalizer (K : Set G) := by
      change Subgroup.closure (Group.conjugatesOfSet (A : Set G)) ≤ _
      rw [Subgroup.closure_le]
      intro y hy
      obtain ⟨a, ha, hay⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hay
      exact hconj c a ha
    rw [htop] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
  refine ⟨hKn, fun hbot => ?_⟩
  have hAC : (A : Set G) ⊆ Subgroup.centralizer (K : Set G) := fun x hx =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((Subgroup.commutator_comm A K).trans hbot) hx
  have hle := Subgroup.normalClosure_le_normal hAC
  rw [htop] at hle
  have hcen : K ≤ Subgroup.center G := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) k hk).symm
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  exact (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2))
    (Quasisimple.perfect_le_center_eq_bot K hcen)

theorem N20 : S_N20 := by
  intro G _ _ S A hA hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, hQA⟩ := N18 G S A hA.le hA.comm hA.closed hA.gen
  have hQn : (CFSG.Open.pCore 2 G).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  have hQp : IsPGroup 2 (CFSG.Open.pCore 2 G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
  have hcent : Subgroup.centralizer (CFSG.Open.pCore 2 G : Set G) ≤ CFSG.Open.pCore 2 G := by
    have h := (N8d G hA.oddCore).2.2
    rwa [hE, sup_bot_eq] at h
  unfold CoreConclusion
  set Q := CFSG.Open.pCore 2 G
  set D := A ⊓ Q
  have hDc : ∀ d ∈ D, ∀ g : G, g⁻¹ * d * g = d := by
    intro d hd g
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (hZ hd) g, ← mul_assoc, inv_mul_cancel, one_mul]
  let H : Subgroup G :=
    { carrier := {x | ∀ q ∈ Q, q⁻¹ * (x⁻¹ * q * x) ∈ D}
      mul_mem' := fun {x y} hx hy q hq => by
        have e : q⁻¹ * ((x * y)⁻¹ * q * (x * y)) =
            (q⁻¹ * (y⁻¹ * q * y)) * (y⁻¹ * (q⁻¹ * (x⁻¹ * q * x)) * y) := by group
        rw [e]
        exact D.mul_mem (hy q hq) (by rw [hDc _ (hx q hq) y]; exact hx q hq)
      one_mem' := fun q _ => by simp
      inv_mem' := fun {x} hx q hq => by
        have h := hx _ (hQn.conj_mem q hq x)
        have e : q⁻¹ * (x⁻¹⁻¹ * q * x⁻¹) =
            ((x * q * x⁻¹)⁻¹ * (x⁻¹ * (x * q * x⁻¹) * x))⁻¹ := by group
        rw [e]
        exact D.inv_mem h }
  have hHn : H.Normal := ⟨fun x hx g q hq => by
    have hq' : g⁻¹ * q * g ∈ Q := by simpa using hQn.conj_mem q hq g⁻¹
    have h := hx _ hq'
    have e : q⁻¹ * ((g * x * g⁻¹)⁻¹ * q * (g * x * g⁻¹)) =
        g * ((g⁻¹ * q * g)⁻¹ * (x⁻¹ * (g⁻¹ * q * g) * x)) * g⁻¹ := by group
    have hd := hDc _ h g⁻¹
    rw [inv_inv] at hd
    rw [e, hd]
    exact h⟩
  have hAH : (A : Set G) ⊆ H := by
    intro a ha q hq
    have h := hQA (Subgroup.commutator_mem_commutator (Q.inv_mem hq) (A.inv_mem ha))
    rw [commutatorElement_def, inv_inv, inv_inv] at h
    simpa [mul_assoc] using h
  have hHtop : ∀ x : G, x ∈ H := by
    intro x
    have h := Subgroup.normalClosure_le_normal (N := H) hAH
    rw [hA.gen] at h
    exact h (Subgroup.mem_top x)
  have hpow : ∀ x q d : G, d ∈ D → x⁻¹ * q * x = q * d → ∀ n : ℕ,
      (x ^ n)⁻¹ * q * x ^ n = q * d ^ n := by
    intro x q d hdD hqd n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (x ^ (n + 1))⁻¹ * q * x ^ (n + 1) = x⁻¹ * ((x ^ n)⁻¹ * q * x ^ n) * x := by
            rw [pow_succ]; group
        _ = (x⁻¹ * q * x) * (x⁻¹ * d ^ n * x) := by rw [ih]; group
        _ = q * d ^ (n + 1) := by rw [hDc _ (D.pow_mem hdD n) x, hqd, pow_succ', mul_assoc]
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQp
  have hQpow : ∀ y ∈ Q, y ^ 2 ^ m = 1 := fun y hy => by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨y, hy⟩ : Q)))
    rwa [hm] at h
  have h2G : IsPGroup 2 G := by
    intro x
    have hxc : x ^ 2 ^ m ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hdD : q⁻¹ * (x⁻¹ * q * x) ∈ D := hHtop x q hq
      have h := hpow x q _ hdD (by group) (2 ^ m)
      rw [hQpow _ hdD.2, mul_one] at h
      calc q * x ^ 2 ^ m = x ^ 2 ^ m * ((x ^ 2 ^ m)⁻¹ * q * x ^ 2 ^ m) := by group
        _ = x ^ 2 ^ m * q := by rw [h]
    refine ⟨m + m, ?_⟩
    rw [pow_add, pow_mul]
    exact hQpow _ (hcent hxc)
  have hStop : (S : Subgroup G) = ⊤ := top_le_iff.mp ((h2G.to_subgroup ⊤).le_sylow_of_normal S)
  have hAn : A.Normal := ⟨fun a ha g => by
    have h := hA.closed a ha g⁻¹ (by rw [hStop]; exact Subgroup.mem_top _)
    simpa using h⟩
  have hAtop : A = ⊤ := (Subgroup.normalClosure_eq_self A).symm.trans hA.gen
  have hQtop : Q = ⊤ := top_le_iff.mp (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore
    2 ⊤ inferInstance (h2G.to_subgroup ⊤))
  refine ⟨hAtop, by rw [hQtop, top_sup_eq], by rw [hAtop, hQtop, top_sup_eq], fun K hK => ?_⟩
  exfalso
  have hKE : K ≤ goldschmidtLayer G := le_sSup hK
  rw [hE] at hKE
  exact (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2)) (le_bot_iff.mp hKE)

end CFSG.Goldschmidt
