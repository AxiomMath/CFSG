module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalTAbelian
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalAbelian

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

structure EndHyp {a : Fin r} (d : DeltaDatum D Abar a) : Prop where
  T_comm : IsMulCommutative d.T
  V_le : AschbacherTheorem3.omegaOne d.S ≤ d.S ⊓
    Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G)
  V_comm : IsMulCommutative (AschbacherTheorem3.omegaOne d.S)
  wcl : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤ d.S ⊔ AschbacherTheorem3.omegaOne d.T →
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S
  card_lt : Nat.card (AschbacherTheorem3.omegaOne d.S) <
    Nat.card (AschbacherTheorem3.omegaOne d.T) *
      Nat.card (AschbacherTheorem3.omegaOne d.S ⊓ factorZStar D Abar a : Subgroup G)

omit [Finite G] in
theorem isElemAbelian_omegaOne {P : Subgroup G} (hP : IsMulCommutative P) :
    IsElemAbelian 2 (AschbacherTheorem3.omegaOne P) := by
  refine ⟨AschbacherTheorem3.isMulCommutative_of_le (AschbacherTheorem3.omegaOne_le P) hP, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
    have hyP : y ∈ P := AschbacherTheorem3.omegaOne_le P hy
    have hzP : z ∈ P := AschbacherTheorem3.omegaOne_le P hz
    have hyz : y * z = z * y := congrArg Subtype.val (hP.is_comm.comm ⟨y, hyP⟩ ⟨z, hzP⟩)
    rw [(Commute.mul_pow hyz 2), ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

omit [Finite G] in
theorem mem_omegaOne {P : Subgroup G} {x : G} (hx : x ∈ P) (hx2 : x ^ 2 = 1) :
    x ∈ AschbacherTheorem3.omegaOne P :=
  Subgroup.subset_closure ⟨hx, hx2⟩

namespace EndHyp

variable {a : Fin r} {d : DeltaDatum D Abar a}

omit [Finite G] in
theorem U_elem (hE : EndHyp d) : IsElemAbelian 2 (AschbacherTheorem3.omegaOne d.T) :=
  isElemAbelian_omegaOne hE.T_comm

omit [Finite G] in
theorem V_elem (hE : EndHyp d) : IsElemAbelian 2 (AschbacherTheorem3.omegaOne d.S) := by
  refine ⟨hE.V_comm, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul y z hy hz ihy ihz =>
    have hyz : y * z = z * y :=
      congrArg Subtype.val (hE.V_comm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
    rw [(Commute.mul_pow hyz 2), ihy, ihz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy, inv_one]

omit [Finite G] in
theorem U_le_T : AschbacherTheorem3.omegaOne d.T ≤ d.T := AschbacherTheorem3.omegaOne_le _

theorem U_inf_A (hC : Counterexample G D r Abar) :
    AschbacherTheorem3.omegaOne d.T ⊓ aschbacherThm5Preimage D (Abar a) = ⊥ := by
  have hT2 : IsPGroup 2 d.T := d.sylowT.isPGroup
  exact eq_bot_of_le_inf_conj hC (datum_g_not_mem d) (hT2.to_le (U_le_T.trans' inf_le_left))
    inf_le_right (inf_le_left.trans (U_le_T.trans (d.sylowT.le.trans inf_le_left)))

omit [Finite G] in
theorem U_le_normalizer_S :
    AschbacherTheorem3.omegaOne d.T ≤ Subgroup.normalizer (d.S : Set G) :=
  U_le_T.trans d.invariant

omit [Finite G] in
theorem U_le_normalizer_A :
    AschbacherTheorem3.omegaOne d.T ≤
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) :=
  U_le_T.trans (d.sylowT.le.trans inf_le_right)

theorem U_le_H (hC : Counterexample G D r Abar) :
    AschbacherTheorem3.omegaOne d.T ≤ Subgroup.normalizer (D : Set G) :=
  U_le_normalizer_A.trans (factor_normalizer_le D r Abar hC.hyp.hii a)

omit [Finite G] in
theorem U_le_L :
    AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g :=
  U_le_T.trans (d.sylowT.le.trans inf_le_left)

theorem U_comm_V (hE : EndHyp d) (hC : Counterexample G D r Abar) :
    ∀ u ∈ AschbacherTheorem3.omegaOne d.T, ∀ v ∈ AschbacherTheorem3.omegaOne d.S,
      u * v = v * u := by
  intro u hu v hv
  have hW : d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ≤
      aschbacherThm5Preimage D (Abar a) ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :=
    inf_le_inf_right _ d.sylowS.le
  refine commute_of_normalizers hC (datum_g_not_mem d) (P := d.S) d.sylowT.le hW
    d.sylowS.isPGroup ?_ u (U_le_T hu) v (hE.V_le hv)
  intro t ht w hw
  have h1 : t⁻¹ * w⁻¹ * t ∈ d.S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (d.invariant ht)) w⁻¹).mp
      (d.S.inv_mem hw.1)
    simpa [mul_assoc] using this
  exact d.S.mul_mem h1 hw.1

omit [Finite G] in
theorem V_le_S : AschbacherTheorem3.omegaOne d.S ≤ d.S := AschbacherTheorem3.omegaOne_le _

theorem mem_V_of_mem_sup (hE : EndHyp d) (hC : Counterexample G D r Abar) {x : G}
    (hx : x ∈ AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S)
    (hxS : x ∈ d.S) : x ∈ AschbacherTheorem3.omegaOne d.S := by
  have hUV : AschbacherTheorem3.omegaOne d.T ≤
      Subgroup.normalizer (AschbacherTheorem3.omegaOne d.S : Set G) := by
    intro u hu
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hE.U_comm_V hC u hu v hv).symm
  have hx' : x ∈ ((AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S :
      Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUV] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have huS : u ∈ d.S := by
    have : u = (u * v) * v⁻¹ := by group
    rw [this]
    exact d.S.mul_mem hxS (d.S.inv_mem (V_le_S hv))
  have hu1 : u ∈ AschbacherTheorem3.omegaOne d.T ⊓ aschbacherThm5Preimage D (Abar a) :=
    ⟨hu, d.sylowS.le huS⟩
  rw [U_inf_A hC, Subgroup.mem_bot] at hu1
  rw [hu1, one_mul]
  exact hv

theorem comm_mem_V (hE : EndHyp d) (hC : Counterexample G D r Abar) :
    ∀ u ∈ AschbacherTheorem3.omegaOne d.T, ∀ s ∈ d.S,
      u⁻¹ * s⁻¹ * u * s ∈ AschbacherTheorem3.omegaOne d.S := by
  intro u hu s hs
  have hle : rightConjugate (AschbacherTheorem3.omegaOne d.T) s ≤
      d.S ⊔ AschbacherTheorem3.omegaOne d.T := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hx' : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    have h1 : s⁻¹ * (s * x * s⁻¹) * s =
        (s⁻¹ * ((s * x * s⁻¹) * s * (s * x * s⁻¹)⁻¹)) * (s * x * s⁻¹) := by group
    have h2 : (s * x * s⁻¹) * s * (s * x * s⁻¹)⁻¹ ∈ d.S :=
      (Subgroup.mem_normalizer_iff.mp (U_le_normalizer_S hx) s).mp hs
    rw [hx', h1]
    exact Subgroup.mul_mem_sup (d.S.mul_mem (d.S.inv_mem hs) h2) hx
  have hconj := hE.wcl s (d.sylowS.le hs) hle
  have hus : s⁻¹ * u * s ∈ AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S := by
    apply hconj
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hu
  have hmem : u⁻¹ * s⁻¹ * u * s ∈
      AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S := by
    have : u⁻¹ * s⁻¹ * u * s = u⁻¹ * (s⁻¹ * u * s) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hu)) hus
  have hmemS : u⁻¹ * s⁻¹ * u * s ∈ d.S := by
    have h1 : u⁻¹ * s⁻¹ * u ∈ d.S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (U_le_normalizer_S hu)) s⁻¹).mp
        (d.S.inv_mem hs)
      simpa [mul_assoc] using this
    exact d.S.mul_mem h1 hs
  exact hE.mem_V_of_mem_sup hC hmem hmemS

end EndHyp

theorem le_rightConjugate_of_le_sup {M N R : Subgroup G} (hM2 : IsPGroup 2 M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hsyl : IsSylowOf 2 (M ⊓ N) N)
    (hR : IsPGroup 2 R) (hRM : R ≤ M ⊔ N) : ∃ n ∈ N, R ≤ rightConjugate M n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hindex : ¬ 2 ∣ M.relIndex (M ⊔ N) := by
    have h1 := Subgroup.relIndex_mul_card M (M ⊔ N)
    rw [inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card N (N ⊔ M)
    rw [inf_eq_left.mpr le_sup_left, AschbacherTheorem3.relIndex_sup_of_le_normalizer hMN] at h2
    have h3 := Subgroup.relIndex_mul_card N M
    rw [sup_comm] at h2
    rw [← h2, ← h3, mul_comm (N.relIndex M)] at h1
    have h4 : M.relIndex (M ⊔ N) * Nat.card (N ⊓ M : Subgroup G) = Nat.card N := by
      have hpos : 0 < N.relIndex M := by
        rcases Nat.eq_zero_or_pos (N.relIndex M) with h | h
        · rw [h, zero_mul] at h3
          exact absurd h3.symm Nat.card_pos.ne'
        · exact h
      have h5 : (M.relIndex (M ⊔ N) * Nat.card (N ⊓ M : Subgroup G)) * N.relIndex M =
          Nat.card N * N.relIndex M := by
        rw [mul_assoc, h1, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right hpos h5
    obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp hsyl
    have h6 := Subgroup.relIndex_mul_card (M ⊓ N) N
    rw [inf_eq_left.mpr inf_le_right] at h6
    rw [inf_comm N M, ← h6] at h4
    have h7 : M.relIndex (M ⊔ N) = (M ⊓ N).relIndex N :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
    rw [h7]
    exact hdvd
  have hMsyl : IsSylowOf 2 M (M ⊔ N) := isSylowOf_iff.mpr ⟨le_sup_left, hM2, hindex⟩
  obtain ⟨c, hc, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hMsyl hR hRM
  have hcinv : c⁻¹ ∈ ((M ⊔ N : Subgroup G) : Set G) := (M ⊔ N).inv_mem hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M N hMN] at hcinv
  obtain ⟨m, hm, n, hn, hmn⟩ := Set.mem_mul.mp hcinv
  refine ⟨n, hn, ?_⟩
  have hRle : R ≤ rightConjugate M c⁻¹ := by
    have h2 : rightConjugate (rightConjugate R c) c⁻¹ ≤ rightConjugate M c⁻¹ :=
      Subgroup.map_mono hle
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h2
  rwa [← hmn, ← rightConjugate_mul, (rightConjugate_eq_self_iff M m).mpr
    (Subgroup.le_normalizer hm)] at hRle

omit [Finite G] in
theorem le_normalizer_factorZStar (i : Fin r) {h : G} (hhH : h ∈ Subgroup.normalizer (D : Set G))
    (hhA : h ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    h ∈ Subgroup.normalizer (factorZStar D Abar i : Set G) := by
  set A := aschbacherThm5Preimage D (Abar i)
  have key : ∀ k : G, k ∈ Subgroup.normalizer (D : Set G) → k ∈ Subgroup.normalizer (A : Set G) →
      ∀ z ∈ factorZStar D Abar i, k * z * k⁻¹ ∈ factorZStar D Abar i := by
    intro k hkH hkA z hz
    obtain ⟨hzA, hzC⟩ := hz
    obtain ⟨hzD, hzc⟩ := (mem_centralizing_iff (Abar i) z).mp hzC
    refine ⟨(Subgroup.mem_normalizer_iff.mp hkA z).mp hzA, (mem_centralizing_iff (Abar i) _).mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hkH z).mp hzD, fun a ha => ?_⟩⟩
    have ha' : k⁻¹ * a * k ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hkA) a).mp ha
      simpa using this
    have h1 := hzc _ ha'
    have heq : (k * z * k⁻¹)⁻¹ * a⁻¹ * (k * z * k⁻¹) * a =
        k * (z⁻¹ * (k⁻¹ * a * k)⁻¹ * z * (k⁻¹ * a * k)) * k⁻¹ := by group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_core D hkH) _).mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key h hhH hhA z, fun hz => ?_⟩
  have h1 := key h⁻¹ (Subgroup.inv_mem _ hhH) (Subgroup.inv_mem _ hhA) _ hz
  simpa [mul_assoc] using h1

namespace EndHyp

variable {a : Fin r} {d : DeltaDatum D Abar a}

theorem conj_le_of_le_sup_zStar (hE : EndHyp d) (hC : Counterexample G D r Abar)
    {c : G} (hc : c ∈ aschbacherThm5Preimage D (Abar a))
    (hle : rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      d.S ⊔ AschbacherTheorem3.omegaOne d.T ⊔ factorZStar D Abar a) :
    rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
      AschbacherTheorem3.omegaOne d.T ⊔ AschbacherTheorem3.omegaOne d.S ⊔
        factorZStar D Abar a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a)
  set U := AschbacherTheorem3.omegaOne d.T
  set V := AschbacherTheorem3.omegaOne d.S
  set Z := factorZStar D Abar a
  have hZA : Z ≤ A := inf_le_left
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := factor_le_normalizer_factorZStar a
  have hUZ : U ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    le_normalizer_factorZStar a (U_le_H hC hu) (U_le_normalizer_A hu)
  have hSU2 : IsPGroup 2 (d.S ⊔ U : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' (d.sylowT.isPGroup.to_le U_le_T) d.sylowS.isPGroup
      U_le_normalizer_S
  have hSUZ : d.S ⊔ U ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le (d.sylowS.le.trans hAZ) hUZ
  have hSUA : (d.S ⊔ U) ⊓ A ≤ d.S := by
    intro x ⟨hx, hxA⟩
    have hx' : x ∈ ((U ⊔ d.S : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U d.S U_le_normalizer_S] at hx'
    obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    have huA : u ∈ A := by
      have : u = (u * s) * s⁻¹ := by group
      rw [this]
      exact A.mul_mem hxA (A.inv_mem (d.sylowS.le hs))
    have hu1 : u ∈ U ⊓ A := ⟨hu, huA⟩
    rw [U_inf_A hC, Subgroup.mem_bot] at hu1
    rw [hu1, one_mul]
    exact hs
  have hsylZ : IsSylowOf 2 ((d.S ⊔ U) ⊓ Z) Z := by
    have heq : (d.S ⊔ U) ⊓ Z = d.S ⊓ Z := by
      apply le_antisymm
      · exact le_inf (le_trans (inf_le_inf_left _ hZA) hSUA) inf_le_right
      · exact inf_le_inf_right _ le_sup_left
    rw [heq]
    exact d.sylowS.inf_of_le_normalizer hZA hAZ
  have hR2 : IsPGroup 2 (rightConjugate U c) :=
    AschbacherTheorem3.isPGroup_rightConjugate (d.sylowT.isPGroup.to_le U_le_T) c
  obtain ⟨z, hz, hzle⟩ := le_rightConjugate_of_le_sup hSU2 hSUZ hsylZ hR2 hle
  have hle' : rightConjugate U (c * z⁻¹) ≤ d.S ⊔ U := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hzle z⁻¹
    rwa [rightConjugate_mul, rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  have hcz : c * z⁻¹ ∈ A := A.mul_mem hc (A.inv_mem (hZA hz))
  have h2 := hE.wcl _ hcz hle'
  have h3 : rightConjugate U c ≤ rightConjugate (U ⊔ V) z := by
    have h4 := AschbacherTheorem3.rightConjugate_le_rightConjugate h2 z
    rwa [rightConjugate_mul, inv_mul_cancel_right] at h4
  refine h3.trans ?_
  have hUVZ : U ⊔ V ≤ Subgroup.normalizer (Z : Set G) :=
    sup_le hUZ ((V_le_S.trans d.sylowS.le).trans hAZ)
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have hx' : x = (z * x * z⁻¹) * ((z * x * z⁻¹)⁻¹ * z⁻¹ * (z * x * z⁻¹) * z) := by group
  rw [hx']
  refine Subgroup.mul_mem_sup hx ?_
  have h5 : (z * x * z⁻¹)⁻¹ * z⁻¹ * (z * x * z⁻¹) ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hUVZ hx)) z⁻¹).mp (Z.inv_mem hz)
    simpa [mul_assoc] using this
  exact Z.mul_mem h5 hz

end EndHyp

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
