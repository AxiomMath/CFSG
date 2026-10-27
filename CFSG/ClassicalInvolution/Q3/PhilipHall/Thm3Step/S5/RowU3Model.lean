module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic
public import CFSG.GH74.KGroups.Generic6
public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3Model
public import Certificates.Certificate516001

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  Certificates.S5Rows Certificates.S5RowsU33

theorem QSA_valid :
    QSA.check = true ∧ QSA.orderCertificate = 64 ∧ leCheck QSA U33.QA = true :=
  Certificates.certificate516001.1

theorem u33RowsF1a_holds : u33RowsF1a () = true :=
  Certificates.certificate516001.2.1

theorem u33RowsF1b_holds : u33RowsF1b () = true :=
  Certificates.certificate516001.2.2.1

theorem u33RowsF1c_holds : u33RowsF1c () = true :=
  Certificates.certificate516001.2.2.2

theorem QSA_ok : ValidSchreier QSA := QSA_valid.1

theorem QP_le_QA : U33.QP.originalSubgroup ≤ U33.QA.originalSubgroup := by
  rw [U33.QP_closure, Subgroup.closure_le]
  intro x hx
  rw [U33.QA, certificate_originalSubgroup]
  apply Subgroup.subset_closure
  rcases hx with rfl | rfl <;> simp

theorem QSA_le_QA :
    QSA.originalSubgroup ≤ U33.QA.originalSubgroup :=
  leCheck_sound QSA U33.QA U33.QA_ok QSA_valid.2.2

abbrev sylowU33 : Subgroup ↥U33.QA.originalSubgroup :=
  QSA.originalSubgroup.subgroupOf U33.QA.originalSubgroup

abbrev u33P : Subgroup ↥U33.QA.originalSubgroup :=
  U33.QP.originalSubgroup.subgroupOf U33.QA.originalSubgroup

theorem card_u33A : Nat.card ↥U33.QA.originalSubgroup = 12096 := by
  rw [card_group U33.QA U33.QA_ok, U33.QA_valid.2]

theorem index_u33P : u33P.index = 2 := by
  have h := Subgroup.card_mul_index u33P
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QP_le_QA).toEquiv, card_group U33.QP U33.QP_ok,
    U33.QP_valid.2, card_u33A] at h
  omega

theorem u33P_normal : u33P.Normal :=
  Subgroup.normal_of_index_eq_two index_u33P

theorem u33_conj_mem_sylow
    (H : Subgroup ↥U33.QA.originalSubgroup) (hH : IsPGroup 2 H) :
    ∃ g : ↥U33.QA.originalSubgroup, ∀ x ∈ H, g⁻¹ * x * g ∈ sylowU33 := by
  have hcard : Nat.card sylowU33 = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSA_le_QA).toEquiv, card_group QSA QSA_ok,
      QSA_valid.2.1]
  refine exists_conj_mem_of_isPGroup (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) ?_ hH
  have h := Subgroup.card_mul_index sylowU33
  rw [hcard, card_u33A] at h
  have h1 : sylowU33.index = 189 := by omega
  rw [h1]
  decide

theorem mem_elemsT_QSA {x : ↥U33.QA.originalSubgroup}
    (hx : x ∈ sylowU33) : (x : Equiv.Perm (Fin 28)) ∈ elemsT QSA :=
  (mem_elemsT QSA QSA_ok _).mpr (Subgroup.mem_subgroupOf.mp hx)

theorem inQP_eq_true_iff {x : ↥U33.QA.originalSubgroup} :
    inQP x = true ↔ x ∈ u33P := by
  rw [Subgroup.mem_subgroupOf, inQP, ← mem_iff_sift U33.QP U33.QP_ok]

theorem Q8Rel.coe_u33 {i j : ↥U33.QA.originalSubgroup} (hij : Q8Rel i j) :
    Q8Rel (i : Equiv.Perm (Fin 28)) (j : Equiv.Perm (Fin 28)) :=
  hij.map U33.QA.originalSubgroup.subtype fun h1 => hij.2.1 (Subtype.ext (by simpa using h1))

theorem mem_q8Span_of_coe {i j x : ↥U33.QA.originalSubgroup}
    (hx : (x : Equiv.Perm (Fin 28)) ∈ q8Span (i : Equiv.Perm (Fin 28)) (j : Equiv.Perm (Fin 28))) :
    x ∈ q8Span i j := by
  obtain ⟨w, hw, hwx⟩ := exists_of_mem_q8Span_map U33.QA.originalSubgroup.subtype hx
  rwa [← Subtype.val_injective hwx]

theorem u33_threeCyc
    {i j : ↥U33.QA.originalSubgroup} (hi : i ∈ sylowU33) (hj : j ∈ sylowU33) (hiP : i ∈ u33P)
    (hjP : j ∈ u33P) (hij : Q8Rel i j) :
    ∃ y : ↥U33.QA.originalSubgroup,
      y⁻¹ * i * y = j ∧ (y⁻¹ * j * y = i * j ∨ y⁻¹ * j * y = j * i) := by
  obtain ⟨y, hy, h1, h2⟩ := threeCycCheck_sound u33RowsF1a_holds (mem_elemsT_QSA hi)
    (mem_elemsT_QSA hj) (inQP_eq_true_iff.mpr hiP) (inQP_eq_true_iff.mpr hjP) hij.coe_u33
  refine ⟨⟨y, QP_le_QA ((mem_elemsT U33.QP U33.QP_ok y).mp hy)⟩, Subtype.ext ?_, ?_⟩
  · simpa using h1
  · rcases h2 with h2 | h2
    · exact Or.inl (Subtype.ext (by simpa using h2))
    · exact Or.inr (Subtype.ext (by simpa using h2))

theorem u33_conjMul
    {i j : ↥U33.QA.originalSubgroup} (hi : i ∈ sylowU33) (hj : j ∈ sylowU33) (hiP : i ∈ u33P)
    (hjP : j ∉ u33P) (hij : Q8Rel i j) :
    ∃ n : ↥U33.QA.originalSubgroup,
      n⁻¹ * i * n ∈ q8Span i j ∧ (n⁻¹ * j * n = j * i ∨ n⁻¹ * j * n = j * i⁻¹) := by
  have hpj : inQP j = false := by
    rw [Bool.eq_false_iff]
    exact fun h1 => hjP (inQP_eq_true_iff.mp h1)
  obtain ⟨n, hn, h1, h2⟩ := conjMulCheck_sound u33RowsF1b_holds (mem_elemsT_QSA hi)
    (mem_elemsT_QSA hj) (inQP_eq_true_iff.mpr hiP) hpj hij.coe_u33
  set n' : ↥U33.QA.originalSubgroup := ⟨n, (mem_elemsT U33.QA U33.QA_ok n).mp hn⟩
  refine ⟨n', mem_q8Span_of_coe (by simpa [n'] using h1), ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl (Subtype.ext (by simpa [n'] using h2))
  · exact Or.inr (Subtype.ext (by simpa [n'] using h2))

theorem u33_uniqueOuter
    {i j i' j' : ↥U33.QA.originalSubgroup} (hi : i ∈ sylowU33) (hj : j ∈ sylowU33)
    (hi' : i' ∈ sylowU33) (hj' : j' ∈ sylowU33) (hij : Q8Rel i j) (hij' : Q8Rel i' j')
    (hout : ¬ (i ∈ u33P ∧ j ∈ u33P)) (hout' : ¬ (i' ∈ u33P ∧ j' ∈ u33P)) :
    i ∈ q8Span i' j' ∧ j ∈ q8Span i' j' := by
  have hp : ∀ a b : ↥U33.QA.originalSubgroup, ¬ (a ∈ u33P ∧ b ∈ u33P) →
      (inQP a && inQP b) = false := by
    intro a b hab
    rw [Bool.eq_false_iff]
    intro h1
    rw [Bool.and_eq_true] at h1
    exact hab ⟨inQP_eq_true_iff.mp h1.1, inQP_eq_true_iff.mp h1.2⟩
  obtain ⟨h1, h2⟩ := uniqueOuterCheck_sound u33RowsF1c_holds (mem_elemsT_QSA hi)
    (mem_elemsT_QSA hj) (mem_elemsT_QSA hi') (mem_elemsT_QSA hj') hij.coe_u33 hij'.coe_u33
    (hp i j hout) (hp i' j' hout')
  exact ⟨mem_q8Span_of_coe h1, mem_q8Span_of_coe h2⟩

theorem centralizer_eq_bot_of_u33 {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hidx : N.index = 2) (hL : LieModel ↥N .PSU 3 3 1) (hX : NoNormalTwo X) :
    Subgroup.centralizer (N : Set X) = ⊥ := by
  obtain ⟨hs, a, b, hab⟩ := PhilipHall.Frame.u33_isSimpleGroup hL
  have hZ : Subgroup.center ↥N = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N) with h | h
    · exact h
    · exfalso
      apply hab
      have h1 : b ∈ Subgroup.center ↥N := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp h1 a)
  have hCN : ∀ c ∈ Subgroup.centralizer (N : Set X), c ∈ N → c = 1 := by
    intro c hc hcN
    have h1 : (⟨c, hcN⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro n
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc n n.2)
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  refine hX _ inferInstance ?_
  rintro ⟨c, hc⟩
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : c * c ∈ N := Subgroup.mul_self_mem_of_index_two hidx c
  have h3 : c * c ∈ Subgroup.centralizer (N : Set X) := Subgroup.mul_mem _ hc hc
  simpa [pow_one, sq] using hCN _ h3 h2

theorem exists_u33_model
    {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hidx : N.index = 2) (hL : LieModel ↥N .PSU 3 3 1)
    (hC : Subgroup.centralizer (N : Set X) = ⊥) :
    ∃ θ : X ≃* ↥U33.QA.originalSubgroup, ∀ x : X, θ x ∈ u33P ↔ x ∈ N := by
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA]
    exact QP_le_QA
  set ψ := M.actHom N with hψ
  have hψi : Function.Injective ψ := M.actHom_injective N hC
  have hψN : ∀ n (hn : n ∈ N), ψ n = (M.e ⟨n, hn⟩ : Equiv.Perm (Fin 28)) := by
    intro n hn
    show (M.Φ (MulAut.conjNormal n) : Equiv.Perm (Fin 28)) = _
    rw [show (MulAut.conjNormal n : MulAut N) = MulAut.conj ⟨n, hn⟩ from
      MulAut.conjNormal_val (h := ⟨n, hn⟩)]
    exact CFSG.ClassicalInvolution.Q3.TA3.autModel_Φ_conj_eq M hPA ⟨n, hn⟩
  have hψA : ∀ x, ψ x ∈ U33.QA.originalSubgroup := fun x => hMA ▸ M.actHom_mem N x
  have hN : Nat.card N = 6048 := by
    rw [Nat.card_congr e.toEquiv, card_group U33.QP U33.QP_ok, U33.QP_valid.2]
  have hXc : Nat.card X = 12096 := by
    have h := Subgroup.card_mul_index N
    rw [hN, hidx] at h
    omega
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  set f : X →* ↥U33.QA.originalSubgroup := ψ.codRestrict _ hψA with hf
  have hfi : Function.Injective f := fun a b hab => by
    have h1 : (f a : Equiv.Perm (Fin 28)) = f b := congrArg Subtype.val hab
    exact hψi h1
  have hbij : Function.Bijective f := hfi.bijective_of_nat_card_le (by rw [hXc, card_u33A])
  refine ⟨MulEquiv.ofBijective f hbij, fun x => ?_⟩
  rw [Subgroup.mem_subgroupOf]
  change ψ x ∈ U33.QP.originalSubgroup ↔ x ∈ N
  constructor
  · intro hx
    rw [← hMP] at hx
    have h1 : ψ ((M.e.symm ⟨ψ x, hx⟩ : N) : X) = ψ x := by
      rw [hψN _ (M.e.symm ⟨ψ x, hx⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
    rw [← hψi h1]
    exact (M.e.symm ⟨ψ x, hx⟩).2
  · intro hx
    rw [hψN x hx, ← hMP]
    exact (M.e ⟨x, hx⟩).2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
