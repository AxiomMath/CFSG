module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56N1
public import CFSG.LocalAnalysis.EvenBN.Tits.S56J

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem s56_lift_mem_liftSub_iff {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD)
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) : d.lift a ∈ d.liftSub X ↔ a ∈ X := by
  constructor
  · intro h
    obtain ⟨x, hx, hxD, hxa⟩ := mem_liftSub.1 h
    rwa [← d.lift_inj hxD ha hxa]
  · intro h
    exact mem_liftSub.2 ⟨a, h, ha, rfl⟩

theorem s56_pv12 (d : Data G) : d.pv 12 = d.z := by
  rw [pv, Model.parrottV_twelve, d.lift_titsZ]

theorem s56_parrottV_mem_titsD {i : ℕ} (hi : i = 9 ∨ i = 10 ∨ i = 11) :
    Model.parrottV i ∈ titsD :=
  (Model.parrottV_mem_titsD_iff (by omega)).2 (by rcases hi with rfl | rfl | rfl <;> decide)

theorem s56_pv10_mem_F (d : Data G) : d.pv 10 ∈ d.F :=
  mem_liftSub.2 ⟨_, Model.parrottV_mem_parrottF (by simp), Model.parrottF_le_titsD
    (Model.parrottV_mem_parrottF (by simp)), rfl⟩

theorem s56_parrottU_eleven_le_titsD : Model.parrottU 11 ≤ titsD :=
  Model.parrottU_eleven_le_ten.trans Model.parrottU_ten_le_titsD

theorem s56_mem_liftSub_U11_iff {x : G} :
    x ∈ d.liftSub (Model.parrottU 11) ↔
      x = 1 ∨ x = d.pv 11 ∨ x = d.z ∨ x = d.pv 11 * d.z := by
  have h11 := s56_parrottV_mem_titsD (i := 11) (by omega)
  have h12 : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]; exact titsZ_mem_titsD
  constructor
  · intro h
    obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 h
    rcases Model.mem_parrottU_eleven_iff.1 hy with rfl | rfl | rfl | rfl
    · left; exact d.lift_one
    · right; left; rfl
    · right; right; left; rw [← s56_pv12 d]; rfl
    · right; right; right
      rw [d.lift_mul h11 h12]
      exact congrArg _ (s56_pv12 d)
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_liftSub.2 ⟨_, Model.mem_parrottU_eleven_iff.2 (Or.inr (Or.inl rfl)), h11, rfl⟩
    · refine mem_liftSub.2 ⟨_, Model.mem_parrottU_eleven_iff.2 (Or.inr (Or.inr (Or.inl rfl))),
        h12, ?_⟩
      rw [← s56_pv12 d]; rfl
    · refine mem_liftSub.2 ⟨_, Model.mem_parrottU_eleven_iff.2 (Or.inr (Or.inr (Or.inr rfl))),
        mul_mem h11 h12, ?_⟩
      rw [d.lift_mul h11 h12]
      show d.pv 11 * d.pv 12 = d.pv 11 * d.z
      rw [s56_pv12 d]

theorem s56U11_eq_liftSub (d : Data G) : d.s56U11 = d.liftSub (Model.parrottU 11) := by
  rw [s56U11_def, s56_pv12]
  apply le_antisymm
  · rw [closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact s56_mem_liftSub_U11_iff.2 (Or.inr (Or.inl rfl))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact s56_mem_liftSub_U11_iff.2 (Or.inr (Or.inr (Or.inl rfl)))
  · intro x hx
    have h1 : d.pv 11 ∈ closure ({d.pv 11, d.z} : Set G) := subset_closure (Set.mem_insert _ _)
    have h2 : d.z ∈ closure ({d.pv 11, d.z} : Set G) :=
      subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases s56_mem_liftSub_U11_iff.1 hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h1
    · exact h2
    · exact mul_mem h1 h2

theorem s56U10_eq_liftSub (d : Data G) : d.s56U10 = d.liftSub (Model.parrottU 10) := by
  have h10 := s56_parrottV_mem_titsD (i := 10) (by omega)
  have h10U : d.pv 10 ∈ d.liftSub (Model.parrottU 10) :=
    mem_liftSub.2 ⟨_, subset_closure ⟨10, by simp, rfl⟩, h10, rfl⟩
  rw [s56U10_def, s56U11_eq_liftSub]
  apply le_antisymm
  · exact sup_le (s56J_liftSub_mono Model.parrottU_eleven_le_ten) ((zpowers_le).2 h10U)
  · intro x hx
    obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hx
    rcases Model.parrottU_ten_cases hy with h | ⟨u, hu, rfl⟩
    · exact mem_sup_left (mem_liftSub.2 ⟨y, h, hyD, rfl⟩)
    · have huD : u ∈ titsD := s56_parrottU_eleven_le_titsD hu
      rw [d.lift_mul h10 huD]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_liftSub.2 ⟨u, hu, huD, rfl⟩))

theorem s56_U11_le_U10 (d : Data G) : d.s56U11 ≤ d.s56U10 := by
  rw [s56U10_def]
  exact le_sup_left

theorem s56_U10_le_F (d : Data G) : d.s56U10 ≤ d.F := by
  rw [s56U10_eq_liftSub]
  exact s56J_liftSub_mono Model.parrottU_ten_le_parrottF

theorem s56_mem_U11_iff {x : G} :
    x ∈ d.s56U11 ↔ x = 1 ∨ x = d.pv 11 ∨ x = d.z ∨ x = d.pv 11 * d.z := by
  rw [s56U11_eq_liftSub]
  exact s56_mem_liftSub_U11_iff

theorem s56_pv11_mem_U11 (d : Data G) : d.pv 11 ∈ d.s56U11 :=
  s56_mem_U11_iff.2 (Or.inr (Or.inl rfl))

theorem s56_z_mem_U11 (d : Data G) : d.z ∈ d.s56U11 :=
  s56_mem_U11_iff.2 (Or.inr (Or.inr (Or.inl rfl)))

theorem s56_pv10_mem_U10 (d : Data G) : d.pv 10 ∈ d.s56U10 := by
  rw [s56U10_def]
  exact mem_sup_right (mem_zpowers _)

theorem s56_pv10_not_mem_U11 (d : Data G) : d.pv 10 ∉ d.s56U11 := fun h => by
  rw [s56U11_eq_liftSub] at h
  exact Model.parrottV_ne.2.2.2
    ((s56_lift_mem_liftSub_iff s56_parrottU_eleven_le_titsD
      (s56_parrottV_mem_titsD (i := 10) (by omega))).1 h)

theorem s56_card_U11 (d : Data G) : Nat.card d.s56U11 = 4 := by
  rw [s56U11_eq_liftSub]
  exact (d.card_liftSub s56_parrottU_eleven_le_titsD).trans Model.card_parrottU_eleven

theorem s56_card_U10 (d : Data G) : Nat.card d.s56U10 = 8 := by
  rw [s56U10_eq_liftSub]
  exact (d.card_liftSub (Model.parrottU_ten_le_parrottF.trans Model.parrottF_le_titsD)).trans
    Model.card_parrottU_ten

theorem s56_U10_cases {x : G} (hx : x ∈ d.s56U10) :
    x ∈ d.s56U11 ∨ ∃ u ∈ d.s56U11, x = d.pv 10 * u := by
  rw [s56U10_eq_liftSub] at hx
  rw [s56U11_eq_liftSub]
  obtain ⟨y, hy, hyD, rfl⟩ := mem_liftSub.1 hx
  rcases Model.parrottU_ten_cases hy with h | ⟨u, hu, rfl⟩
  · exact Or.inl (mem_liftSub.2 ⟨y, h, hyD, rfl⟩)
  · have h10 := s56_parrottV_mem_titsD (i := 10) (by omega)
    have huD : u ∈ titsD := s56_parrottU_eleven_le_titsD hu
    exact Or.inr ⟨d.lift u, mem_liftSub.2 ⟨u, hu, huD, rfl⟩, d.lift_mul h10 huD⟩

theorem Hyp.s56_lift_mem_CNt (hd : d.Hyp) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsN) :
    d.lift x ∈ d.N ⊓ centralizer ({d.t} : Set G) := by
  have hC : d.lift x ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem x)
  refine mem_inf.2 ⟨(hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD hC).2 ?_, hC⟩
  rw [hd.ρ_lift (titsN_le_titsD hx)]
  rw [← Model.titsD_inf_normalizer_parrottF] at hx
  exact (mem_inf.1 hx).2

theorem Hyp.s56_rho_mem_twoF4N (hd : d.Hyp) {c : G}
    (hc : c ∈ d.N ⊓ centralizer ({d.t} : Set G)) :
    (d.ρ ⟨c, (mem_inf.1 hc).2⟩ : Equiv.Perm (Fin 1755)) ∈ CFSG.Quasithin.twoF4N := by
  rw [← Model.titsA_inf_normalizer_parrottF]
  exact mem_inf.2 ⟨(d.ρ ⟨c, (mem_inf.1 hc).2⟩).2,
    (hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD (mem_inf.1 hc).2).1 (mem_inf.1 hc).1⟩

@[expose] noncomputable def s56Y (d : Data G) : G := d.lift Model.nlocY

theorem Hyp.s56_Y_facts (hd : d.Hyp) :
    d.s56Y ∈ d.N ⊓ centralizer ({d.t} : Set G) ∧ d.s56Y ∈ d.L ∧ d.s56Y ^ 3 = 1 ∧
      d.s56Y ≠ 1 ∧ d.s56Y * d.pv 10 = d.pv 10 * d.s56Y ∧
      d.s56Y * d.pv 11 * d.s56Y⁻¹ = d.z ∧ d.s56Y * d.z * d.s56Y⁻¹ = d.pv 11 * d.z := by
  obtain ⟨hyN, hy3, hy1, hy10, hy11, hy12⟩ := Model.nlocY_facts
  have hyD : Model.nlocY ∈ titsD := titsN_le_titsD hyN
  have h10 := s56_parrottV_mem_titsD (i := 10) (by omega)
  have h11 := s56_parrottV_mem_titsD (i := 11) (by omega)
  have h12 : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]; exact titsZ_mem_titsD
  refine ⟨hd.s56_lift_mem_CNt hyN, d.lift_mem _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s56Y, ← d.lift_pow hyD, hy3, d.lift_one]
  · intro h
    exact hy1 (d.lift_inj hyD (one_mem _) (by rw [d.lift_one]; exact h))
  · exact (d.lift_comm_iff hyD h10).2 hy10
  · have h := d.lift_conj hyD h11
    rw [hy11] at h
    exact h.symm.trans (s56_pv12 d)
  · have h := d.lift_conj hyD h12
    rw [hy12, d.lift_mul h11 h12] at h
    have e : d.lift (Model.parrottV 12) = d.z := s56_pv12 d
    rw [e] at h
    exact h.symm

@[expose] noncomputable def s56K (d : Data G) : Subgroup G := d.liftSub titsK

theorem Hyp.s56_K_le_CNt (hd : d.Hyp) : d.s56K ≤ d.N ⊓ centralizer ({d.t} : Set G) := by
  intro k hk
  obtain ⟨x, hx, hxD, rfl⟩ := mem_liftSub.1 hk
  exact hd.s56_lift_mem_CNt (titsK_le_titsN hx)

theorem s56_card_K (d : Data G) : Nat.card d.s56K = 1024 :=
  (d.card_liftSub titsK_le_titsD).trans titsQK_facts.2.2.2

theorem s56_K_isPGroup (d : Data G) : IsPGroup 2 d.s56K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 10) (by rw [s56_card_K]; norm_num)

theorem s56_twoF4N_le_normalizer_titsK :
    CFSG.Quasithin.twoF4N ≤ normalizer (titsK : Set (Equiv.Perm (Fin 1755))) := by
  intro x hx
  have hx' : x ∈ titsN ∨ x * CFSG.Quasithin.tπ⁻¹ ∈ titsN := hx
  rcases hx' with h | h
  · exact (titsN_le_NK h).2
  · have h2 := mul_mem (titsN_le_NK h).2 CFSG.Quasithin.tπ_norm_K
    simpa using h2

theorem Hyp.s56_conj_K (hd : d.Hyp) {c : G} (hc : c ∈ d.N ⊓ centralizer ({d.t} : Set G))
    {k : G} (hk : k ∈ d.s56K) : c * k * c⁻¹ ∈ d.s56K := by
  have hmap := hd.map_conj_liftSub (mem_inf.1 hc).2 (titsK_le_titsD : titsK ≤ titsD)
  have hρK := s56_twoF4N_le_normalizer_titsK (hd.s56_rho_mem_twoF4N hc)
  have hnorm : titsK.map (MulAut.conj (d.ρ ⟨c, (mem_inf.1 hc).2⟩ :
      Equiv.Perm (Fin 1755))).toMonoidHom = titsK :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hρK
  rw [hnorm] at hmap
  have hk' : c * k * c⁻¹ ∈ (d.liftSub titsK).map (MulAut.conj c).toMonoidHom :=
    ⟨k, hk, rfl⟩
  rw [hmap] at hk'
  exact hk'

theorem Hyp.s56_K_le_P0 (h49 : d.Thm49Statement) (hd : d.Hyp) : d.s56K ≤ d.s56P0 :=
  hd.s56_le_P0_of_normal_CNt h49 (s56_K_isPGroup d) hd.s56_K_le_CNt fun _ hc _ hk =>
    hd.s56_conj_K hc hk

theorem s56_kword_prod_mem {w : List ℕ} (hw : w ∈ Certificates.TitsAschbacherNLocal.kWords) :
    d.lift (w.map Model.parrottV).prod ∈ d.s56K :=
  mem_liftSub.2 ⟨_, Model.kWords_mem_titsK w hw, titsK_le_titsD (Model.kWords_mem_titsK w hw),
    rfl⟩

theorem s56_CF_K_le_U11 {x : G} (hx : x ∈ d.F) (hc : ∀ k ∈ d.s56K, x * k = k * x) :
    x ∈ d.s56U11 := by
  rw [s56U11_eq_liftSub]
  obtain ⟨x', hx'F, hx'D, rfl⟩ := mem_liftSub.1 hx
  refine mem_liftSub.2 ⟨x', Model.mem_parrottU_eleven_of_comm hx'F (fun w hw => ?_), hx'D, rfl⟩
  have hk := Model.kWords_mem_titsK w hw
  exact (d.lift_comm_iff hx'D (titsK_le_titsD hk)).1 (hc _ (s56_kword_prod_mem hw))

theorem s56_comm_K_le_U10 {x : G} (hx : x ∈ d.F)
    (hc : ∀ k ∈ d.s56K, k * x * k⁻¹ * x⁻¹ ∈ d.s56U11) : x ∈ d.s56U10 := by
  rw [s56U11_eq_liftSub] at hc
  rw [s56U10_eq_liftSub]
  obtain ⟨x', hx'F, hx'D, rfl⟩ := mem_liftSub.1 hx
  refine mem_liftSub.2 ⟨x', Model.mem_parrottU_ten_of_comm hx'F (fun w hw => ?_), hx'D, rfl⟩
  have hk := Model.kWords_mem_titsK w hw
  have hkD := titsK_le_titsD hk
  have h := hc _ (s56_kword_prod_mem hw)
  rw [← s56J_lift_commutator hkD hx'D] at h
  exact (s56_lift_mem_liftSub_iff s56_parrottU_eleven_le_titsD
    (mul_mem (mul_mem (mul_mem hkD hx'D) (inv_mem hkD)) (inv_mem hx'D))).1 h

theorem s56_Y_comm_not_mem {x : G} (hx : x ∈ d.F) (hx10 : x ∉ d.s56U10) :
    d.s56Y * x * d.s56Y⁻¹ * x⁻¹ ∉ d.s56U10 := by
  rw [s56U10_eq_liftSub] at hx10 ⊢
  obtain ⟨x', hx'F, hx'D, rfl⟩ := mem_liftSub.1 hx
  have hx'10 : x' ∉ Model.parrottU 10 := fun h => hx10 (mem_liftSub.2 ⟨x', h, hx'D, rfl⟩)
  have hyD : Model.nlocY ∈ titsD := titsN_le_titsD Model.nlocY_facts.1
  intro h
  rw [s56Y, ← s56J_lift_commutator hyD hx'D] at h
  exact Model.nlocY_comm_not_mem hx'F hx'10
    ((s56_lift_mem_liftSub_iff (Model.parrottU_ten_le_parrottF.trans Model.parrottF_le_titsD)
      (mul_mem (mul_mem (mul_mem hyD hx'D) (inv_mem hyD)) (inv_mem hx'D))).1 h)

theorem s56_kElt_facts :
    d.lift (Model.parrottV 4 * Model.parrottV 5) ∈ d.s56K ∧
      d.lift (Model.parrottV 1 * Model.parrottV 5) ∈ d.s56K ∧
      d.lift (Model.parrottV 4 * Model.parrottV 5) * d.pv 10 *
          (d.lift (Model.parrottV 4 * Model.parrottV 5))⁻¹ = d.z * d.pv 10 ∧
      d.lift (Model.parrottV 1 * Model.parrottV 5) * d.pv 10 *
          (d.lift (Model.parrottV 1 * Model.parrottV 5))⁻¹ = d.pv 11 * d.pv 10 := by
  obtain ⟨h1, h2⟩ := Model.kElt_facts
  have h45 : (([4, 5] : List ℕ).map Model.parrottV).prod ∈ titsK :=
    Model.kWords_mem_titsK [4, 5] (by decide)
  have h15 : (([1, 5] : List ℕ).map Model.parrottV).prod ∈ titsK :=
    Model.kWords_mem_titsK [1, 5] (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h45 h15
  have h45D := titsK_le_titsD h45
  have h15D := titsK_le_titsD h15
  have h10 := s56_parrottV_mem_titsD (i := 10) (by omega)
  have h11 := s56_parrottV_mem_titsD (i := 11) (by omega)
  have h12 : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]; exact titsZ_mem_titsD
  refine ⟨mem_liftSub.2 ⟨_, h45, h45D, rfl⟩, mem_liftSub.2 ⟨_, h15, h15D, rfl⟩, ?_, ?_⟩
  · have h := d.lift_conj h45D h10
    have e : d.lift (Model.parrottV 12) = d.z := s56_pv12 d
    rw [h1, d.lift_mul h12 h10, e] at h
    exact h.symm
  · have h := d.lift_conj h15D h10
    rw [h2, d.lift_mul h11 h10] at h
    exact h.symm

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
