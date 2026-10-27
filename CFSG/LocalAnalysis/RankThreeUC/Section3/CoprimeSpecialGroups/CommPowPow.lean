module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section3

namespace CoprimeSpecialGroups

open Subgroup

open scoped commutatorElement

section GroupLevel

variable {G : Type*} [Group G]

theorem class_two [Finite G] [Group.IsNilpotent G]
    (hchar : ∀ V : Subgroup G, V.Characteristic → IsMulCommutative V → V ≤ center G) :
    commutator G ≤ center G := by
  by_contra hcon
  have hl2 : (⊤ : Subgroup G).lowerCentralSeries 2 ≠ ⊥ := by
    intro h
    apply hcon
    rw [Subgroup.lowerCentralSeries_succ, top_lowerCentralSeries_one] at h
    exact commutator_top_right_eq_bot_iff_le_center.mp h
  have hex := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  classical
  set n0 := Nat.find hex with hn0
  have h0 : (⊤ : Subgroup G).lowerCentralSeries n0 = ⊥ := Nat.find_spec hex
  have h3 : 3 ≤ n0 := by
    by_contra hlt
    apply hl2
    rw [eq_bot_iff, ← h0]
    exact Subgroup.lowerCentralSeries_antitone _ (by omega : n0 ≤ 2)
  obtain ⟨m, hm⟩ : ∃ m, n0 = m + 2 := ⟨n0 - 2, by omega⟩
  have hne : (⊤ : Subgroup G).lowerCentralSeries (m + 1) ≠ ⊥ :=
    Nat.find_min hex (by omega : m + 1 < n0)
  have hm1 : 1 ≤ m := by omega
  have hcent : (⊤ : Subgroup G).lowerCentralSeries (m + 1) ≤ center G := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [← Subgroup.lowerCentralSeries_succ, ← hm]; exact h0
  have hZ2c : ⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆ ≤ center G := by
    rw [commutator_le]
    intro x hx y _
    have := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hx y
    rwa [Subgroup.upperCentralSeries_one] at this
  have hMZ2 : (⊤ : Subgroup G).lowerCentralSeries m ≤ Subgroup.upperCentralSeries G 2 := by
    intro x hx
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    apply hcent
    rw [Subgroup.lowerCentralSeries_succ]
    exact commutator_mem_commutator hx (mem_top y)
  have h3s : ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆, Subgroup.upperCentralSeries G 2⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (H₃ := Subgroup.upperCentralSeries G 2) ?_ ?_
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G)]
      exact commutator_top_right_eq_bot_iff_le_center.mpr hZ2c
    · exact commutator_top_right_eq_bot_iff_le_center.mpr hZ2c
  have hM1 : (⊤ : Subgroup G).lowerCentralSeries m ≤ commutator G :=
    Subgroup.lowerCentralSeries_antitone _ hm1
  haveI : IsMulCommutative ((⊤ : Subgroup G).lowerCentralSeries m) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : (a : G) ∈ (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) := hM1 a.2
    have h2 := hMZ2 b.2
    have h4 : ⁅(a : G), (b : G)⁆ ∈ (⊥ : Subgroup G) := h3s ▸ commutator_mem_commutator h1 h2
    apply Subtype.ext
    have := (mem_bot.mp h4)
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hle := hchar ((⊤ : Subgroup G).lowerCentralSeries m) inferInstance inferInstance
  exact hne (commutator_top_right_eq_bot_iff_le_center.mpr hle)

theorem comm_pow_pow {x y : G} (h : ⁅x, y⁆ ∈ center G) (a b : ℕ) :
    ⁅x ^ a, y ^ b⁆ = ⁅x, y⁆ ^ (a * b) := by
  have hc : ∀ g : G, Commute g ⁅x, y⁆ := fun g => ((mem_center_iff.mp h) g)
  have h1 : ⁅x ^ a, y⁆ = ⁅x, y⁆ ^ a := ((hc x).commutatorElement_pow_left a).symm
  have h2 : Commute y ⁅x ^ a, y⁆ := by rw [h1]; exact (hc y).pow_right a
  rw [← (h2.commutatorElement_pow_right b), h1, pow_mul]

theorem exp_p [Finite G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G)
    (hcc : commutator G ≤ center G)
    (hchar : ∀ V : Subgroup G, V.Characteristic → IsMulCommutative V → V ≤ center G) :
    ∀ x : G, x ^ p ∈ center G := by
  have hcomm : ∀ x y : G, ⁅x, y⁆ ∈ center G := fun x y =>
    hcc (commutator_mem_commutator (mem_top x) (mem_top y))
  have step : ∀ n : ℕ, 1 ≤ n → (∀ x : G, x ^ (p ^ (n + 1)) ∈ center G) →
      ∀ x : G, x ^ (p ^ n) ∈ center G := by
    intro n hn hP
    set W : Subgroup G := closure (Set.range fun x : G => x ^ (p ^ n)) with hW
    haveI : W.Characteristic := by
      rw [characteristic_iff_map_le]
      intro φ
      rw [hW, MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact subset_closure ⟨φ x, by simp⟩
    haveI : IsMulCommutative W := by
      apply isMulCommutative_closure
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
      show _ * _ = _ * _
      have h1 := comm_pow_pow (hcomm x y) (p ^ n) (p ^ n)
      have h2 : ⁅x ^ (p ^ (n + 1)), y ^ (p ^ (n - 1))⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact ((mem_center_iff.mp (hP x)) _).symm
      have h3 := comm_pow_pow (hcomm x y) (p ^ (n + 1)) (p ^ (n - 1))
      have h4 : p ^ n * p ^ n = p ^ (n + 1) * p ^ (n - 1) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h5 : ⁅x ^ (p ^ n), y ^ (p ^ n)⁆ = 1 := by rw [h1, h4, ← h3, h2]
      exact commutatorElement_eq_one_iff_mul_comm.mp h5
    have hle := hchar W inferInstance inferInstance
    intro x
    exact hle (subset_closure ⟨x, rfl⟩)
  obtain ⟨N, hN⟩ := hG.exists_exponent_dvd_pow
  have hall : ∀ k : ℕ, (∀ x : G, x ^ (p ^ (1 + k)) ∈ center G) → ∀ x : G, x ^ (p ^ 1) ∈ center G := by
    intro k
    induction k with
    | zero => intro h; exact h
    | succ k ih =>
      intro h
      apply ih
      exact step (1 + k) (by omega) h
  have := hall N (by
    intro x
    have : x ^ (p ^ (1 + N)) = 1 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one] at hN
      rw [add_comm, pow_succ]
      rw [pow_mul, hN x, one_pow]
    rw [this]; exact one_mem _)
  intro x
  simpa using this x

theorem commutator_le_frattini [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    commutator G ≤ frattini G := by
  haveI : Group.IsNilpotent G := hG.isNilpotent
  unfold frattini Order.radical
  refine le_iInf₂ fun M hM => ?_
  haveI : M.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom M hM
  have hpr := (Subgroup.isCoatom_iff_index_prime M).mp hM
  haveI : Fact (Nat.card (G ⧸ M)).Prime := ⟨by rwa [← Subgroup.index]⟩
  haveI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card rfl
  rw [commutator_def, commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' M ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (IsCyclic.commGroup (α := G ⧸ M)).mul_comm _ _

theorem frattini_elem_abelian {Q : Type*} [CommGroup Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    (h : ∀ x : Q, x ^ p = 1) : frattini Q = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  by_contra hg1
  rw [mem_bot] at hg1
  haveI : Module (ZMod p) (Additive Q) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      apply Additive.toMul.injective
      simpa using h (Additive.toMul x))
  haveI : Module.Free (ZMod p) (Additive Q) := Module.Free.of_divisionRing _ _
  haveI : Module.Projective (ZMod p) (Additive Q) := inferInstance
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) (V := Additive Q)
    (x := Additive.ofMul g) (by simpa using hg1)
  let φ : Q →* Multiplicative (ZMod p) := AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom
  have hφg : φ g ≠ 1 := by
    intro h1
    apply hf
    exact h1
  have hrange : Nat.card φ.range = p := by
    have hd : Nat.card φ.range ∣ p := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      simpa [Nat.card_eq_fintype_card, ZMod.card] using this
    rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
    · exfalso
      rw [Subgroup.card_eq_one] at h1
      apply hφg
      have : φ g ∈ φ.range := ⟨g, rfl⟩
      rw [h1] at this
      exact this
    · exact h1
  have hker : IsCoatom φ.ker := by
    apply Subgroup.isCoatom_of_index_prime
    rw [Subgroup.index_ker, hrange]; exact hp.out
  have := frattini_le_coatom hker hg
  exact hφg (MonoidHom.mem_ker.mp this)

end GroupLevel
section XLevel

variable {X : Type*} [Group X]

theorem centralizes_of_B (S B U : Subgroup X) (hSB : ⁅S, B⁆ = S) (hUS : ⁅U, S⁆ ≤ U)
    (hBU : B ≤ centralizer (U : Set X)) : S ≤ centralizer (U : Set X) := by
  have hBU' : ⁅B, U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hBU
  have h : ⁅⁅S, B⁆, U⁆ = ⊥ := by
    refine commutator_commutator_eq_bot_of_rotate (H₁ := S) (H₂ := B) (H₃ := U) ?_ ?_
    · rw [hBU']; exact Subgroup.commutator_bot_left S
    · rw [eq_bot_iff]
      exact le_trans (Subgroup.commutator_mono_left hUS) (by rw [Subgroup.commutator_comm U B, hBU'])
  rw [hSB] at h
  exact commutator_eq_bot_iff_le_centralizer.mp h

def cj (S : Subgroup X) (b : X) (hb : b ∈ normalizer (S : Set X)) : S →* S where
  toFun s := ⟨b * s * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb s).mp s.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

theorem fixed_mem_commutator [Finite X] {p : ℕ} (S B : Subgroup X) (hS : IsPGroup p S)
    (hB : Nat.Coprime p (Nat.card B)) (hBS : B ≤ normalizer (S : Set X)) (hSB : ⁅S, B⁆ = S)
    (c : S) (hc : ∀ b ∈ B, b * c * b⁻¹ = c) : c ∈ commutator S := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  let g : B → (S →* Abelianization S) := fun b => (Abelianization.of).comp (cj S b.1 (hBS b.2))
  let φ : S →* Abelianization S := ∏ b : B, g b
  have hφ : ∀ s, φ s = ∏ b : B, Abelianization.of (cj S b.1 (hBS b.2) s) := by
    intro s; simp [φ, g, MonoidHom.finset_prod_apply]
  have h1 : ∀ b' : B, ∀ s, φ (cj S b'.1 (hBS b'.2) s) = φ s := by
    intro b' s
    rw [hφ, hφ]
    refine Fintype.prod_equiv (Equiv.mulRight b') _ _ ?_
    intro b
    congr 1
    ext; simp [cj, mul_assoc]
  have h2 : ⁅S, B⁆ ≤ (φ.ker).map S.subtype := by
    rw [commutator_le]
    intro s hs b hb
    refine ⟨⟨s, hs⟩ * cj S b (hBS hb) ⟨s, hs⟩⁻¹, ?_, ?_⟩
    · change φ _ = 1
      have h3 : φ (cj S b (hBS hb) ⟨s, hs⟩⁻¹) = φ ⟨s, hs⟩⁻¹ := h1 ⟨b, hb⟩ _
      rw [map_mul, h3, map_inv, mul_inv_cancel]
    · simp [cj, commutatorElement_def, mul_assoc]
  have hcK : c ∈ φ.ker := by
    have hcS : (c : X) ∈ (φ.ker).map S.subtype := h2 (by rw [hSB]; exact c.2)
    obtain ⟨x, hx, hxc⟩ := hcS
    have : x = c := Subtype.ext hxc
    exact this ▸ hx
  have h4 : φ c = Abelianization.of c ^ Nat.card B := by
    rw [hφ]
    have : ∀ b : B, Abelianization.of (cj S b.1 (hBS b.2) c) = Abelianization.of c := by
      intro b
      congr 1
      exact Subtype.ext (hc b.1 b.2)
    simp only [this, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have h5 : Abelianization.of c ^ Nat.card B = 1 := h4 ▸ hcK
  obtain ⟨k, hk⟩ := hS c
  have hd1 : orderOf (Abelianization.of c) ∣ Nat.card B := orderOf_dvd_of_pow_eq_one h5
  have hd2 : orderOf (Abelianization.of c) ∣ p ^ k := by
    have := orderOf_map_dvd (Abelianization.of : S →* Abelianization S) c
    exact this.trans (orderOf_dvd_of_pow_eq_one hk)
  have hd : orderOf (Abelianization.of c) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hB.pow_left k) hd2 hd1
  rw [orderOf_eq_one_iff] at hd
  rw [← Abelianization.ker_of]
  exact hd

end XLevel
variable {X : Type} [Group X]

def IsSpecialPGroup (S : Subgroup X) : Prop :=
  (center S).map S.subtype = (commutator S).map S.subtype ∧
    (center S).map S.subtype = (frattini S).map S.subtype

theorem exists_characteristic_abelian_not_centralized_or_special_center_eq_centralizer [Finite X] (p : ℕ) (hp : p.Prime) (S B : Subgroup X)
    (hS : IsPGroup p S) (hSne : S ≠ ⊥) (hB : Nat.Coprime p (Nat.card B))
    (hBS : B ≤ normalizer (S : Set X)) (hSB : ⁅S, B⁆ = S) :
    (∃ U : Subgroup X, U ≤ S ∧ (U.subgroupOf S).Characteristic ∧ IsMulCommutative U ∧
        ¬ B ≤ centralizer (U : Set X)) ∨
      (IsSpecialPGroup S ∧ (center S).map S.subtype = S ⊓ centralizer (B : Set X)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases h1 : ∃ U : Subgroup X, U ≤ S ∧ (U.subgroupOf S).Characteristic ∧ IsMulCommutative U ∧
      ¬ B ≤ centralizer (U : Set X)
  · exact Or.inl h1
  right
  push Not at h1
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hnorm : ∀ U : Subgroup X, U ≤ S → (U.subgroupOf S).Characteristic → ⁅U, S⁆ ≤ U := by
    intro U hUS hUc
    haveI := hUc
    haveI : (U.subgroupOf S).Normal := inferInstance
    rw [commutator_le]
    intro u hu s hs
    have h := (inferInstance : (U.subgroupOf S).Normal).conj_mem ⟨u, hUS hu⟩⁻¹
      (inv_mem (mem_subgroupOf.mpr hu)) ⟨s, hs⟩
    have h' : s * u⁻¹ * s⁻¹ ∈ U := h
    have : ⁅u, s⁆ = u * (s * u⁻¹ * s⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem hu h'
  have hchar : ∀ V : Subgroup S, V.Characteristic → IsMulCommutative V → V ≤ center S := by
    intro V hV hVc
    have hUS : V.map S.subtype ≤ S := by
      rintro _ ⟨x, _, rfl⟩; exact x.2
    have hsub : (V.map S.subtype).subgroupOf S = V := by
      rw [← comap_subtype]; exact comap_map_eq_self_of_injective S.subtype_injective V
    have hUc : ((V.map S.subtype).subgroupOf S).Characteristic := by rw [hsub]; exact hV
    have hBU := h1 _ hUS hUc inferInstance
    have hSU := centralizes_of_B S B _ hSB (hnorm _ hUS hUc) hBU
    intro v hv
    rw [mem_center_iff]
    intro g
    have := (mem_centralizer_iff.mp (hSU g.2)) v.1 ⟨v, hv, rfl⟩
    exact Subtype.ext this.symm
  have hcc := class_two hchar
  have hpow := exp_p hp hS hcc hchar
  have hBcent : ∀ z : S, z ∈ center S → ∀ b ∈ B, b * (z : X) * b⁻¹ = z := by
    intro z hz b hb
    have hUS : (center S).map S.subtype ≤ S := by
      rintro _ ⟨x, _, rfl⟩; exact x.2
    have hsub : ((center S).map S.subtype).subgroupOf S = center S := by
      rw [← comap_subtype]; exact comap_map_eq_self_of_injective S.subtype_injective _
    have hUc : ((center S).map S.subtype).subgroupOf S |>.Characteristic := by
      rw [hsub]; infer_instance
    haveI : IsMulCommutative ((center S).map S.subtype) := inferInstance
    have hBU := h1 _ hUS hUc inferInstance
    have := mem_centralizer_iff.mp (hBU hb) z ⟨z, hz, rfl⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hZle : center S ≤ commutator S := fun z hz =>
    fixed_mem_commutator S B hS hB hBS hSB z (hBcent z hz)
  have heq : center S = commutator S := le_antisymm hZle hcc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [heq]
  · have hfr : center S = frattini S := by
      apply le_antisymm
      · rw [heq]; exact commutator_le_frattini hS
      · have h2 := frattini_le_comap_frattini_of_surjective
          (φ := (Abelianization.of : S →* Abelianization S)) (fun x => QuotientGroup.induction_on x (fun a => ⟨a, rfl⟩))
        have h3 : frattini (Abelianization S) = ⊥ := by
          apply frattini_elem_abelian (p := p)
          intro x
          refine QuotientGroup.induction_on x (fun y => ?_)
          show Abelianization.of y ^ p = 1
          rw [← map_pow, ← MonoidHom.mem_ker, Abelianization.ker_of, ← heq]
          exact hpow y
        rw [h3, MonoidHom.comap_bot, Abelianization.ker_of, ← heq] at h2
        exact h2
    rw [hfr]
  · ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      show (z : X) ∈ centralizer (B : Set X)
      rw [mem_centralizer_iff]
      intro b hb
      have := hBcent z hz b hb
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · rintro ⟨hxS, hxB⟩
      refine ⟨⟨x, hxS⟩, ?_, rfl⟩
      rw [heq]
      apply fixed_mem_commutator S B hS hB hBS hSB
      intro b hb
      have := mem_centralizer_iff.mp hxB b hb
      rw [mul_inv_eq_iff_eq_mul]
      exact this

end CoprimeSpecialGroups
end Section3
end CFSG.LocalAnalysis.RankThreeUC
