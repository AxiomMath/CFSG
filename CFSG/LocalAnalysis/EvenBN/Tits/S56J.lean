module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Five
public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Ten
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.NLocal

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

section NoCerts

variable {G : Type} [Group G] {d : Data G}

@[expose] noncomputable def s56J (d : Data G) : Subgroup G := d.liftSub titsJ

theorem s56_J_le_L (d : Data G) : d.s56J ≤ d.L := d.liftSub_le _

theorem Hyp.s56_x5_mem_L (d : Data G) : d.x₅ ∈ d.L := d.lift_mem _

theorem s56J_liftSub_mono {X Y : Subgroup (Equiv.Perm (Fin 1755))} (h : X ≤ Y) :
    d.liftSub X ≤ d.liftSub Y := by
  intro g hg
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 hg
  exact mem_liftSub.2 ⟨x, h hx, hxD, rfl⟩

theorem s56J_lift_commutator {x y : Equiv.Perm (Fin 1755)} (hx : x ∈ titsD) (hy : y ∈ titsD) :
    d.lift (x * y * x⁻¹ * y⁻¹) = d.lift x * d.lift y * (d.lift x)⁻¹ * (d.lift y)⁻¹ := by
  rw [d.lift_mul (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy), d.lift_conj hx hy,
    d.lift_inv hy]

theorem s56J_lift_mem_zpowers
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ zpowers titsZ) :
    d.lift x ∈ zpowers d.z := by
  rcases (Model.mem_zpowers_of_orderOf_two orderOf_titsZ).1 hx with rfl | rfl
  · rw [d.lift_one]
    exact one_mem _
  · rw [d.lift_titsZ]
    exact mem_zpowers _

end NoCerts

section NoCertsFinite

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.s56_x5_comm_t (hd : d.Hyp) : d.x₅ * d.t = d.t * d.x₅ :=
  hd.L_comm_t (Hyp.s56_x5_mem_L d)

end NoCertsFinite

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem s56J_titsJ_le_twoF4P : titsJ ≤ CFSG.Quasithin.twoF4P := fun x hx => by
  rw [← (Model.pCore_twoF4H).2.2.1] at hx
  exact hx.1

theorem s56J_parrottV_mem_titsJ {i : ℕ} (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) :
    Model.parrottV i ∈ titsJ := by
  have hi3 : 3 ≤ i ∧ i ≤ 12 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have hP : Model.parrottV i ∈ CFSG.Quasithin.twoF4P := by
    rw [Model.twoF4P_eq_parrottU_three]
    exact subset_closure ⟨i, hi3, rfl⟩
  have hD : Model.parrottV i ∈ titsD := Model.parrottF_le_titsD (Model.parrottV_mem_parrottF hi)
  rw [← (Model.pCore_twoF4H).2.2.1]
  exact mem_inf.2 ⟨hP, hD⟩

theorem s56J_parrottF_le_titsJ : Model.parrottF ≤ titsJ := by
  rw [Model.parrottF, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact s56J_parrottV_mem_titsJ hi

theorem s56J_E_comm {a b : G} (ha : a ∈ d.E) (hb : b ∈ d.E) : a * b = b * a :=
  (d.liftSub_elemAbelian Model.card_hatE.2.2.1 Model.card_hatE.2.1).1 a ha b hb

theorem s56_E_le_J (d : Data G) : d.E ≤ d.s56J :=
  s56J_liftSub_mono Model.hatE_le_titsJ

theorem s56_F_le_J (d : Data G) : d.F ≤ d.s56J :=
  s56J_liftSub_mono s56J_parrottF_le_titsJ

theorem s56_pv_mem_J (d : Data G) {i : ℕ} (hi : i ∈ ({7, 9, 10, 11, 12} : Set ℕ)) :
    d.pv i ∈ d.s56J :=
  mem_liftSub.2 ⟨Model.parrottV i, s56J_parrottV_mem_titsJ hi,
    titsJ_le_titsD (s56J_parrottV_mem_titsJ hi), rfl⟩

theorem Hyp.s56_J_le_M (hd : d.Hyp) : d.s56J ≤ d.M := by
  intro j hj
  obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hj
  have hjC : d.lift y ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem y)
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hyN : y ∈ titsD ⊓ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
    rw [Model.titsD_inf_normalizer_hatE]
    exact titsJ_le_titsH hy
  show d.lift y ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hjC, hd.ρ_lift hyD]
  exact hyN.2

theorem Hyp.s56_J_comm_E (hd : d.Hyp) {j e : G} (hj : j ∈ d.s56J) (he : e ∈ d.E) :
    j * e * j⁻¹ * e⁻¹ ∈ zpowers d.z := by
  obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hj
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 he
  have hc : x * y * x⁻¹ * y⁻¹ ∈ zpowers titsZ :=
    Model.comm_hatE.2.1 x hx y (s56J_titsJ_le_twoF4P hy)
  have hc' : y * x * y⁻¹ * x⁻¹ ∈ zpowers titsZ := by
    have h := inv_mem hc
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e] at h
  rw [← s56J_lift_commutator hyD hxD]
  exact s56J_lift_mem_zpowers hc'

theorem Hyp.s56_J_le_Q0 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56J ≤ d.s56Q0 := by
  intro j hj
  have h := (hd.s56_structure_M h49).2.2.2.1
  have hmem : j ∈ (d.s56Q0 : Set G) := by
    rw [h]
    exact ⟨hd.s56_J_le_M hj, fun e he => hd.s56_J_comm_E hj he⟩
  exact hmem

theorem Hyp.s56_J_inf_Q2 (hd : d.Hyp) : d.s56J ⊓ d.s56Q2 = d.E := by
  apply le_antisymm
  · rintro j ⟨hj, hjQ⟩
    have hjQ' : j ∈ d.M ⊓ centralizer (d.E : Set G) := hjQ
    have hjc := mem_centralizer_iff.1 (mem_inf.1 hjQ').2
    obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hj
    have hyC : y ∈ titsJ ⊓ centralizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
      refine mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun x hx => ?_⟩
      have hxD : x ∈ titsD := titsJ_le_titsD (Model.hatE_le_titsJ hx)
      exact (d.lift_comm_iff hxD hyD).1 (hjc (d.lift x) (mem_liftSub.2 ⟨x, hx, hxD, rfl⟩))
    rw [Model.tits_vertex_hatE.2.2.1] at hyC
    exact mem_liftSub.2 ⟨y, hyC, hyD, rfl⟩
  · intro e he
    refine ⟨d.s56_E_le_J he, ?_⟩
    have : e ∈ d.M ⊓ centralizer (d.E : Set G) :=
      mem_inf.2 ⟨d.s56_E_le_M he, mem_centralizer_iff.2 fun e' he' => s56J_E_comm he' he⟩
    exact this

theorem Hyp.s56_card_J (hd : d.Hyp) : Nat.card d.s56J = 2 ^ 9 := by
  rw [s56J, d.card_liftSub titsJ_le_titsD, titsQJ_facts.2.2.2]
  norm_num

theorem Hyp.s56_J_isPGroup (hd : d.Hyp) : IsPGroup 2 d.s56J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 9) hd.s56_card_J

theorem Hyp.s56_J_comm_le_E (hd : d.Hyp) {j j' : G} (hj : j ∈ d.s56J) (hj' : j' ∈ d.s56J) :
    j * j' * j⁻¹ * j'⁻¹ ∈ d.E := by
  obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hj
  obtain ⟨y', hy', hy'D, rfl⟩ := mem_liftSub.1 hj'
  have hc : y * y' * y⁻¹ * y'⁻¹ ∈ Model.hatE :=
    Model.comm_hatE.1 y (s56J_titsJ_le_twoF4P hy) y' (s56J_titsJ_le_twoF4P hy')
  have hcD : y * y' * y⁻¹ * y'⁻¹ ∈ titsD :=
    mul_mem (mul_mem (mul_mem hyD hy'D) (inv_mem hyD)) (inv_mem hy'D)
  rw [← s56J_lift_commutator hyD hy'D]
  exact mem_liftSub.2 ⟨_, hc, hcD, rfl⟩

theorem Hyp.s56_exists_comm_eq_z (hd : d.Hyp) :
    ∃ a ∈ d.s56J, ∃ b ∈ d.s56J, a * b * a⁻¹ * b⁻¹ = d.z := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Model.comm_hatE.2.2
  have hxJ : x ∈ titsJ := Model.hatE_le_titsJ hx
  have hxD := titsJ_le_titsD hxJ
  have hyD := titsJ_le_titsD hy
  refine ⟨d.lift x, mem_liftSub.2 ⟨x, hxJ, hxD, rfl⟩, d.lift y,
    mem_liftSub.2 ⟨y, hy, hyD, rfl⟩, ?_⟩
  rw [← s56J_lift_commutator hxD hyD, hxy, d.lift_titsZ]

theorem Hyp.s56_L_inf_M_normalizes_J (hd : d.Hyp) {h : G} (hhL : h ∈ d.L) (hhM : h ∈ d.M) :
    h ∈ normalizer (d.s56J : Set G) := by
  have hC : h ∈ centralizer ({d.t} : Set G) := hd.L_le hhL
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  obtain ⟨a, haD, rfl⟩ : ∃ a ∈ titsD, d.lift a = h :=
    ⟨((d.θ ⟨h, hhL⟩ : titsD) : Equiv.Perm (Fin 1755)), (d.θ ⟨h, hhL⟩).2, d.lift_θ ⟨h, hhL⟩⟩
  have hρ := hd.ρ_lift haD
  have haN : a ∈ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
    have h1 := (hd.mem_normalizer_tSup_iff hED hC).1 hhM
    rwa [hρ] at h1
  have haH : a ∈ titsH := by
    rw [← Model.titsD_inf_normalizer_hatE]
    exact mem_inf.2 ⟨haD, haN⟩
  have hJ : a ∈ normalizer (titsJ : Set (Equiv.Perm (Fin 1755))) :=
    CFSG.Quasithin.titsH_le_normalizer_titsJ haH
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap := hd.map_conj_liftSub hC titsJ_le_titsD
  have hn : titsJ.map (MulAut.conj a).toMonoidHom = titsJ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hJ
  rw [hρ, hn] at hmap
  exact hmap

section X5


theorem Hyp.s56_x5_comm_z (hd : d.Hyp) : d.x₅ * d.z = d.z * d.x₅ := by
  have hXH := Model.hatX_facts.1
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  have hc : Model.hatX * titsZ = titsZ * Model.hatX :=
    mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hXH)
  rw [x₅, ← d.lift_titsZ]
  exact d.lift_comm hXD titsZ_mem_titsD hc

theorem Hyp.s56_orderOf_x5 (hd : d.Hyp) : orderOf d.x₅ = 5 := by
  rw [x₅, d.orderOf_lift (titsH_le_titsD Model.hatX_facts.1)]
  exact Model.hatX_facts.2.1

theorem Hyp.s56_x5_mem_M (hd : d.Hyp) : d.x₅ ∈ d.M := by
  have hXH := Model.hatX_facts.1
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD hXH
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have hC : d.x₅ ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem _)
  have hXN : Model.hatX ∈ titsD ⊓ normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) := by
    rw [Model.titsD_inf_normalizer_hatE]
    exact hXH
  show d.x₅ ∈ normalizer ((d.liftSub Model.hatE ⊔ zpowers d.t : Subgroup G) : Set G)
  rw [hd.mem_normalizer_tSup_iff hED hC]
  have hρ : (d.ρ ⟨d.x₅, hC⟩ : Equiv.Perm (Fin 1755)) = Model.hatX := hd.ρ_lift hXD
  rw [hρ]
  exact hXN.2

theorem Hyp.s56_x5_normalizes_J (hd : d.Hyp) : d.x₅ ∈ normalizer (d.s56J : Set G) :=
  hd.s56_L_inf_M_normalizes_J (Hyp.s56_x5_mem_L d) hd.s56_x5_mem_M

theorem Hyp.s56_J_cent_x5 (hd : d.Hyp) {j : G} (hj : j ∈ d.s56J) (hc : j * d.x₅ = d.x₅ * j) :
    j ∈ zpowers d.z := by
  obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hj
  have hXD : Model.hatX ∈ titsD := titsH_le_titsD Model.hatX_facts.1
  have hcomm : y * Model.hatX = Model.hatX * y := (d.lift_comm_iff hyD hXD).1 hc
  have h12 : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]
    exact titsZ_mem_titsD
  rcases Model.hatX_facts.2.2.2.2 y (s56J_titsJ_le_twoF4P hy) hcomm with h | h | h | h
  · rw [h, d.lift_one]
    exact one_mem _
  · exact absurd (h ▸ hyD) Model.parrottV_five.2.1
  · rw [h, Model.parrottV_twelve, d.lift_titsZ]
    exact mem_zpowers _
  · refine absurd ?_ Model.parrottV_five.2.1
    have h' := mul_mem hyD (inv_mem h12)
    rwa [h, mul_inv_cancel_right] at h'

theorem Hyp.s56_E_cent_x5 (hd : d.Hyp) {e : G} (he : e ∈ d.E) (hc : e * d.x₅ = d.x₅ * e) :
    e ∈ zpowers d.z :=
  hd.s56_J_cent_x5 (d.s56_E_le_J he) hc

end X5

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
