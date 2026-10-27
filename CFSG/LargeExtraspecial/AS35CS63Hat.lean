module

public import CFSG.LargeExtraspecial.AS35CS63Wall

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace S63

variable {G : Type} [Group G] {S : Setting G}

theorem mem_QG_of_centralizes [Finite G] {t m : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) (hm : m ∈ S.M)
    (hmc : ∀ e ∈ S.QG, e * t = t * e → m * e = e * m) : m ∈ S.QG := by
  refine S.mem_QG_of_cl_conj hm fun w hw => ?_
  have hwQ' : m * w * m⁻¹ ∈ S.QG := S.conj_mem_QG hm hw
  have hdQ : m * w * m⁻¹ * w⁻¹ ∈ S.QG := S.QG.mul_mem hwQ' (S.QG.inv_mem hw)
  have hfixe : ∀ e ∈ S.QG, e * t = t * e → rhoG S hm (S.cl e) = S.cl e := by
    intro e he het
    rw [rhoG_cl hm he]
    congr 1
    rw [hmc e he het]
    group
  have hd : m * w * m⁻¹ * w⁻¹ ∈
      S.QG ⊓ centralizer ((S.QG ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    refine ⟨hdQ, mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨heQ, het⟩ := mem_inf.mp he
    rw [mem_centralizer_singleton_iff] at het
    rw [← S.polar_cl_eq_zero_iff heQ hdQ, cl_commutator hm hw, QuadraticMap.polar_sub_right]
    have h1 : polar S.q (S.cl e) (rhoG S hm (S.cl w)) = polar S.q (S.cl e) (S.cl w) := by
      conv_lhs => rw [← hfixe e heQ het]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (rhoG_mem hm) _ _
    rw [h1, sub_self]
  have hq : S.q (S.cl (m * w * m⁻¹)) = S.q (S.cl w) := by
    rw [← rhoG_cl hm hw]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (rhoG_mem hm) _
  have hqt : S.q (S.cl t) = 0 := (S.q_cl_eq_zero_iff htQ).mpr (by rw [pow_two]; exact ht2)
  have key : S.cl (m * w * m⁻¹) = S.cl t + S.cl w → S.cl (m * w * m⁻¹) = S.cl w := by
    intro h
    have h1 : polar S.q (S.cl t) (S.cl w) = 0 := by
      have := hq
      rw [h, map_add_eq, hqt, zero_add] at this
      linear_combination this
    rw [S.polar_cl_eq_zero_iff htQ hw] at h1
    have h2 := hfixe w hw h1.symm
    rwa [rhoG_cl hm hw] at h2
  have hsplit : S.cl (m * w * m⁻¹) = S.cl (m * w * m⁻¹ * w⁻¹) + S.cl w := by
    rw [← S.cl_mul hdQ hw]
    congr 1
    group
  rcases (S.mem_centralizer_centralizer_iff htQ).mp hd with h | h | h | h
  · rw [hsplit, h, S.cl_one, zero_add]
  · rw [hsplit, h, S.cl_z, zero_add]
  · exact key (by rw [hsplit, h])
  · exact key (by rw [hsplit, h, S.cl_mul_z htQ])

theorem eq_of_centralizes [Finite G] {t m : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) (hm : m ∈ S.M)
    (hmc : ∀ e ∈ S.QG, e * t = t * e → m * e = e * m) :
    m = 1 ∨ m = S.z ∨ m = t ∨ m = t * S.z := by
  refine (S.mem_centralizer_centralizer_iff htQ).mp
    ⟨mem_QG_of_centralizes htQ ht2 hm hmc, mem_centralizer_iff.mpr fun e he => ?_⟩
  obtain ⟨heQ, het⟩ := mem_inf.mp he
  rw [mem_centralizer_singleton_iff] at het
  exact (hmc e heQ het).symm

variable (S) in
@[expose] def Z2 (t : G) : Subgroup G := closure ({S.z, t} : Set G)

section Z2

variable {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1)
include htQ ht2

theorem mem_Z2_iff {a : G} : a ∈ Z2 S t ↔ a = 1 ∨ a = S.z ∨ a = t ∨ a = S.z * t :=
  mem_closure_pair_iff S.z_mul_z ht2 (S.z_comm_QG htQ).symm

theorem mem_Z2_of {a : G} (ha : a = 1 ∨ a = S.z ∨ a = t ∨ a = t * S.z) : a ∈ Z2 S t := by
  rw [mem_Z2_iff htQ ht2]
  rcases ha with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, S.z_comm_QG htQ])))

theorem comm_of_mem_Z2 {a u : G} (ha : a ∈ Z2 S t) (hu : u ∈ S.M) (hut : u * t = t * u) :
    u * a = a * u := by
  rcases (mem_Z2_iff htQ ht2).mp ha with rfl | rfl | rfl | rfl
  · group
  · exact S.z_comm hu
  · exact hut
  · calc u * (S.z * t) = (u * S.z) * t := by group
      _ = S.z * (u * t) := by rw [S.z_comm hu]; group
      _ = S.z * t * u := by rw [hut]; group

theorem mul_self_of_mem_Z2 {a : G} (ha : a ∈ Z2 S t) : a * a = 1 := by
  rcases (mem_Z2_iff htQ ht2).mp ha with rfl | rfl | rfl | rfl
  · group
  · exact S.z_mul_z
  · exact ht2
  · calc S.z * t * (S.z * t) = S.z * (t * S.z) * t := by group
      _ = S.z * (S.z * t) * t := by rw [S.z_comm_QG htQ]
      _ = (S.z * S.z) * (t * t) := by group
      _ = 1 := by rw [S.z_mul_z, ht2, one_mul]

theorem Z2_le_M : Z2 S t ≤ S.M := fun a ha => by
  rcases (mem_Z2_iff htQ ht2).mp ha with rfl | rfl | rfl | rfl
  · exact S.M.one_mem
  · exact S.z_mem_M
  · exact S.QG_le_M htQ
  · exact S.M.mul_mem S.z_mem_M (S.QG_le_M htQ)

theorem comm_t_of_mem_Z2 {a : G} (ha : a ∈ Z2 S t) : a * t = t * a :=
  (comm_of_mem_Z2 htQ ht2 ha (S.QG_le_M htQ) rfl).symm

end Z2

variable (S) in
@[expose] def Hhat {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) : Subgroup G where
  carrier := {u | u ∈ S.M ∧ u * t = t * u ∧
    ∀ e ∈ S.QG, e * t = t * e → u * e * u⁻¹ * e⁻¹ ∈ Z2 S t}
  mul_mem' := by
    rintro u v ⟨huM, hut, hu⟩ ⟨hvM, hvt, hv⟩
    refine ⟨S.M.mul_mem huM hvM, by rw [mul_assoc, hvt, ← mul_assoc, hut, mul_assoc], ?_⟩
    intro e he het
    have e1 : u * v * e * (u * v)⁻¹ * e⁻¹ =
        u * (v * e * v⁻¹ * e⁻¹) * u⁻¹ * (u * e * u⁻¹ * e⁻¹) := by group
    have h1 : u * (v * e * v⁻¹ * e⁻¹) * u⁻¹ = v * e * v⁻¹ * e⁻¹ := by
      rw [comm_of_mem_Z2 htQ ht2 (hv e he het) huM hut]
      group
    rw [e1, h1]
    exact mul_mem (hv e he het) (hu e he het)
  one_mem' := ⟨S.M.one_mem, by group, fun e _ _ => by
    rw [show (1 : G) * e * 1⁻¹ * e⁻¹ = 1 by group]
    exact one_mem _⟩
  inv_mem' := by
    rintro u ⟨huM, hut, hu⟩
    refine ⟨S.M.inv_mem huM, ?_, ?_⟩
    · calc u⁻¹ * t = u⁻¹ * (t * u) * u⁻¹ := by group
        _ = t * u⁻¹ := by rw [← hut]; group
    · intro e he het
      have h1 := hu e he het
      have e1 : u⁻¹ * e * u⁻¹⁻¹ * e⁻¹ = u⁻¹ * (u * e * u⁻¹ * e⁻¹)⁻¹ * u := by group
      have hc := comm_of_mem_Z2 htQ ht2 (inv_mem h1) huM hut
      have h2 : u⁻¹ * (u * e * u⁻¹ * e⁻¹)⁻¹ * u = (u * e * u⁻¹ * e⁻¹)⁻¹ := by
        calc u⁻¹ * (u * e * u⁻¹ * e⁻¹)⁻¹ * u = u⁻¹ * ((u * e * u⁻¹ * e⁻¹)⁻¹ * u) := by group
          _ = u⁻¹ * (u * (u * e * u⁻¹ * e⁻¹)⁻¹) := by rw [← hc]
          _ = (u * e * u⁻¹ * e⁻¹)⁻¹ := by group
      rw [e1, h2]
      exact inv_mem h1

theorem z_mem_Hhat {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) : S.z ∈ Hhat S htQ ht2 :=
  ⟨S.z_mem_M, (S.z_comm_QG htQ).symm, fun e he _ => by
    rw [show S.z * e * S.z⁻¹ * e⁻¹ = 1 by rw [← S.z_comm_QG he]; group]
    exact one_mem _⟩

theorem mem_Hhat_of_mem_QG {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) {f : G}
    (hf : f ∈ S.QG) (hft : f * t = t * f) : f ∈ Hhat S htQ ht2 :=
  ⟨S.QG_le_M hf, hft, fun e he _ => by
    rcases S.commutator_eq_one_or_z hf he with h | h <;> rw [h]
    · exact one_mem _
    · exact subset_closure (by simp)⟩

theorem exists_conj_of_mem_Hhat {t : G} {htQ : t ∈ S.QG} {ht2 : t * t = 1} {u : G}
    (hu : u ∈ Hhat S htQ ht2) {e : G} (he : e ∈ S.QG) (het : e * t = t * e) :
    ∃ ε ∈ Z2 S t, u * e * u⁻¹ = ε * e ∧ u⁻¹ * e * u = ε * e := by
  have hε := hu.2.2 e he het
  set ε := u * e * u⁻¹ * e⁻¹ with hε_def
  have hεε := mul_self_of_mem_Z2 htQ ht2 hε
  have hεu := comm_of_mem_Z2 htQ ht2 hε hu.1 hu.2.1
  have hεe : u * e * u⁻¹ = ε * e := by rw [hε_def]; group
  refine ⟨ε, hε, hεe, ?_⟩
  have hεu' : u⁻¹ * ε = ε * u⁻¹ := by
    calc u⁻¹ * ε = u⁻¹ * (ε * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * ε) * u⁻¹ := by rw [hεu]
      _ = ε * u⁻¹ := by group
  calc u⁻¹ * e * u = u⁻¹ * (ε * ε) * e * u := by rw [hεε]; group
    _ = (u⁻¹ * ε) * (ε * e) * u := by group
    _ = ε * (u⁻¹ * (u * e * u⁻¹) * u) := by rw [hεu', hεe]; group
    _ = ε * e := by group

section HhatConj

variable {t : G} {htQ : t ∈ S.QG} {ht2 : t * t = 1}

theorem conj_mem_of_mem_Hhat {u : G} (hu : u ∈ Hhat S htQ ht2) {e : G} (he : e ∈ S.QG)
    (het : e * t = t * e) : u * e * u⁻¹ ∈ S.QG ∧ (u * e * u⁻¹) * t = t * (u * e * u⁻¹) := by
  refine ⟨S.conj_mem_QG hu.1 he, ?_⟩
  have hut' : u⁻¹ * t = t * u⁻¹ := by
    calc u⁻¹ * t = u⁻¹ * (t * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * t) * u⁻¹ := by rw [hu.2.1]
      _ = t * u⁻¹ := by group
  calc (u * e * u⁻¹) * t = u * e * (u⁻¹ * t) := by group
    _ = u * (e * t) * u⁻¹ := by rw [hut']; group
    _ = (u * t) * e * u⁻¹ := by rw [het]; group
    _ = t * (u * e * u⁻¹) := by rw [hu.2.1]; group

theorem inv_conj_eq_of_mem_Hhat {u : G} (hu : u ∈ Hhat S htQ ht2) {e : G} (he : e ∈ S.QG)
    (het : e * t = t * e) : u⁻¹ * e * u = u * e * u⁻¹ := by
  obtain ⟨ε, -, h1, h2⟩ := exists_conj_of_mem_Hhat hu he het
  rw [h1, h2]

theorem conj_conj_self_of_mem_Hhat {u : G} (hu : u ∈ Hhat S htQ ht2) {e : G} (he : e ∈ S.QG)
    (het : e * t = t * e) : u * (u * e * u⁻¹) * u⁻¹ = e := by
  rw [← inv_conj_eq_of_mem_Hhat hu he het]
  group

theorem conj_comm_of_mem_Hhat {u v : G} (hu : u ∈ Hhat S htQ ht2) (hv : v ∈ Hhat S htQ ht2)
    {e : G} (he : e ∈ S.QG) (het : e * t = t * e) :
    u * (v * e * v⁻¹) * u⁻¹ = v * (u * e * u⁻¹) * v⁻¹ := by
  obtain ⟨εu, hεu, hu1, -⟩ := exists_conj_of_mem_Hhat hu he het
  obtain ⟨εv, hεv, hv1, -⟩ := exists_conj_of_mem_Hhat hv he het
  have c1 := comm_of_mem_Z2 htQ ht2 hεv hu.1 hu.2.1
  have c2 := comm_of_mem_Z2 htQ ht2 hεu hv.1 hv.2.1
  have c3 := comm_of_mem_Z2 htQ ht2 hεv (Z2_le_M htQ ht2 hεu) (comm_t_of_mem_Z2 htQ ht2 hεu)
  rw [hu1, hv1]
  calc u * (εv * e) * u⁻¹ = (u * εv) * e * u⁻¹ := by group
    _ = εv * (u * e * u⁻¹) := by rw [c1]; group
    _ = εv * εu * e := by rw [hu1]; group
    _ = εu * εv * e := by rw [← c3]
    _ = εu * (v * e * v⁻¹) := by rw [hv1]; group
    _ = (v * εu) * e * v⁻¹ := by rw [c2]; group
    _ = v * (εu * e) * v⁻¹ := by group

end HhatConj

theorem sq_mem_Z2_of_mem_Hhat [Finite G] {t : G} {htQ : t ∈ S.QG} {ht2 : t * t = 1} {u : G}
    (hu : u ∈ Hhat S htQ ht2) : u * u ∈ Z2 S t := by
  refine mem_Z2_of htQ ht2 (eq_of_centralizes htQ ht2 (S.M.mul_mem hu.1 hu.1) fun e he het => ?_)
  calc u * u * e = (u * (u * e * u⁻¹) * u⁻¹) * (u * u) := by group
    _ = e * (u * u) := by rw [conj_conj_self_of_mem_Hhat hu he het]

theorem commutator_mem_Z2_of_mem_Hhat [Finite G] {t : G} {htQ : t ∈ S.QG} {ht2 : t * t = 1}
    {u v : G} (hu : u ∈ Hhat S htQ ht2) (hv : v ∈ Hhat S htQ ht2) :
    u * v * u⁻¹ * v⁻¹ ∈ Z2 S t := by
  have hm : u * v * u⁻¹ * v⁻¹ ∈ Hhat S htQ ht2 :=
    mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
  refine mem_Z2_of htQ ht2 (eq_of_centralizes htQ ht2 hm.1 fun e he het => ?_)
  have h1 := conj_mem_of_mem_Hhat hv he het
  have key : (u * v * u⁻¹ * v⁻¹) * e * (u * v * u⁻¹ * v⁻¹)⁻¹ = e := by
    calc (u * v * u⁻¹ * v⁻¹) * e * (u * v * u⁻¹ * v⁻¹)⁻¹
        = u * (v * (u⁻¹ * (v⁻¹ * e * v) * u) * v⁻¹) * u⁻¹ := by group
      _ = u * (v * (u * (v * e * v⁻¹) * u⁻¹) * v⁻¹) * u⁻¹ := by
          rw [inv_conj_eq_of_mem_Hhat hv he het, inv_conj_eq_of_mem_Hhat hu h1.1 h1.2]
      _ = u * (v * (v * (u * e * u⁻¹) * v⁻¹) * v⁻¹) * u⁻¹ := by
          rw [conj_comm_of_mem_Hhat hu hv he het]
      _ = e := by
          have h3 := conj_mem_of_mem_Hhat hu he het
          rw [conj_conj_self_of_mem_Hhat hv h3.1 h3.2, conj_conj_self_of_mem_Hhat hu he het]
  calc (u * v * u⁻¹ * v⁻¹) * e
      = ((u * v * u⁻¹ * v⁻¹) * e * (u * v * u⁻¹ * v⁻¹)⁻¹) * (u * v * u⁻¹ * v⁻¹) := by group
    _ = e * (u * v * u⁻¹ * v⁻¹) := by rw [key]

theorem isPGroup_Hhat [Finite G] {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) :
    IsPGroup 2 (Hhat S htQ ht2) := by
  intro u
  refine ⟨2, Subtype.ext ?_⟩
  have h := mul_self_of_mem_Z2 htQ ht2 (sq_mem_Z2_of_mem_Hhat u.2)
  change (u : G) ^ (2 ^ 2) = 1
  rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  exact h

theorem commutator_commutator_Hhat [Finite G] {t : G} (htQ : t ∈ S.QG) (ht2 : t * t = 1) :
    ⁅⁅Hhat S htQ ht2, Hhat S htQ ht2⁆, Hhat S htQ ht2⁆ = ⊥ := by
  rw [eq_bot_iff, commutator_le]
  intro a ha w hw
  rw [mem_bot]
  have hsub : ⁅Hhat S htQ ht2, Hhat S htQ ht2⁆ ≤ centralizer (Hhat S htQ ht2 : Set G) := by
    rw [commutator_le]
    intro u hu v hv
    rw [mem_centralizer_iff]
    intro y hy
    rw [commutatorElement_def]
    exact (comm_of_mem_Z2 htQ ht2 (commutator_mem_Z2_of_mem_Hhat hu hv) hy.1 hy.2.1)
  have hac := mem_centralizer_iff.mp (hsub ha) w hw
  rw [commutatorElement_def]
  calc a * w * a⁻¹ * w⁻¹ = (w * a) * a⁻¹ * w⁻¹ := by rw [← hac]
    _ = 1 := by group

end S63

end CFSG.LargeExtraspecial
