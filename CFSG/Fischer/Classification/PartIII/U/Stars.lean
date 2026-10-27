module

public import CFSG.Fischer.Classification.PartIII.U.Flag
public import CFSG.Fischer.Classification.Unitary.Mu

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.Fischer.Classification.LocalR3
  CFSG.ClassicalGroups.Unitary

variable {n : ℕ}

noncomputable abbrev sv (α : K) (x : Fin n → K) : Fin (n + 2) → K := α • v₀ n + ι n x

theorem π_sv (α : K) (x : Fin n → K) : π n (sv α x) = x := by
  rw [sv, map_add, map_smul, π_v₀, smul_zero, zero_add, π_ι]

theorem herm_v₀_sv (α : K) (x : Fin n → K) : herm frob (v₀ n) (sv α x) = 0 := by
  rw [sv, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]

theorem herm_u₀_sv (α : K) (x : Fin n → K) : herm frob (u₀ n) (sv α x) = α := by
  rw [sv, herm_add_right, herm_smul_right, herm_u₀_v₀, herm_u₀_ι, mul_one, add_zero]

theorem herm_sv_sv (α α' : K) (x x' : Fin n → K) :
    herm frob (sv α x) (sv α' x') = herm frob x x' := by
  rw [herm_eq_coords, herm_v₀_sv, herm_v₀_sv, π_sv, π_sv, mul_zero, map_zero, zero_mul,
    zero_add, zero_add]

theorem sv_ne_zero (α : K) {x : Fin n → K} (hx : x ≠ 0) : sv α x ≠ 0 := fun h =>
  hx (by rw [← π_sv α x, h, map_zero])

theorem sv_ne_smul_v₀ (α : K) {x : Fin n → K} (hx : x ≠ 0) (c : K) : sv α x ≠ c • v₀ n :=
  fun h => hx (by rw [← π_sv α x, h, map_smul, π_v₀, smul_zero])

theorem smul_sv (c α : K) (x : Fin n → K) : c • sv α x = sv (c * α) (c • x) := by
  rw [sv, sv, smul_add, smul_smul, map_smul]

theorem sv_add (α α' : K) (x x' : Fin n → K) : sv α x + sv α' x' = sv (α + α') (x + x') := by
  rw [sv, sv, sv, add_smul, map_add]
  abel

theorem tq_sv_mem_localClass (hn : 1 ≤ n) (α : K) {x : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) : tq (sv α x) ∈ LocalClass (DG (n + 2)) (tq (v₀ n)) :=
  (tq_mem_localClass_iff (by omega) v₀_ne_zero herm_v₀_v₀ (sv_ne_zero α hx0)
    (by rw [herm_sv_sv]; exact hx)).2 ⟨herm_v₀_sv α x, sv_ne_smul_v₀ α hx0⟩

theorem exists_sv_of_mem_localClass (hn : 1 ≤ n) {q : PG (n + 2)}
    (hq : q ∈ LocalClass (DG (n + 2)) (tq (v₀ n))) :
    ∃ α x, x ≠ 0 ∧ herm frob x x = 0 ∧ q = tq (sv α x) := by
  rw [localClass_DG (by omega) v₀_ne_zero herm_v₀_v₀] at hq
  obtain ⟨w, hw0, hw, hvw, hwv, rfl⟩ := hq
  have hdec := decomp_of_perp hvw
  have hπ0 : π n w ≠ 0 := fun h => by
    have h1 := hdec
    rw [h, map_zero, add_zero] at h1
    exact hwv _ h1
  refine ⟨herm frob (u₀ n) w, π n w, hπ0, ?_, by rw [sv, ← hdec]⟩
  have h1 := herm_sv_sv (herm frob (u₀ n) w) (herm frob (u₀ n) w) (π n w) (π n w)
  rwa [sv, ← hdec, hw, eq_comm] at h1

theorem isotropic_sv (α : K) {x : Fin n → K} (hx : herm frob x x = 0) :
    herm frob (sv α x) (sv α x) = 0 := by
  rw [herm_sv_sv]; exact hx

theorem tq_sv_eq_tq_sv_iff (hn : 1 ≤ n) {α α' : K} {x x' : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hx0' : x' ≠ 0) (hx' : herm frob x' x' = 0) :
    tq (sv α x) = tq (sv α' x') ↔ ∃ c : K, x' = c • x ∧ α' = c * α := by
  rw [tq_eq_tq_iff (by omega) (sv_ne_zero α hx0) (isotropic_sv α hx) (sv_ne_zero α' hx0')
    (isotropic_sv α' hx')]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, ?_⟩
    · have := congrArg (π n) hc
      rwa [π_sv, map_smul, π_sv] at this
    · have := congrArg (herm frob (u₀ n)) hc
      rwa [herm_u₀_sv, herm_smul_right, herm_u₀_sv] at this
  · rintro ⟨c, hx'c, hα'c⟩
    exact ⟨c, by rw [smul_sv, hx'c, hα'c]⟩

theorem tq_sv_commute_iff (hn : 1 ≤ n) {α α' : K} {x x' : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hx0' : x' ≠ 0) (hx' : herm frob x' x' = 0) :
    tq (sv α x) * tq (sv α' x') = tq (sv α' x') * tq (sv α x) ↔ herm frob x x' = 0 := by
  rw [tq_commute_iff (by omega) (sv_ne_zero α hx0) (isotropic_sv α hx) (sv_ne_zero α' hx0')
    (isotropic_sv α' hx'), herm_sv_sv]

theorem tq_sv_mul_mul {α α' : K} {x x' : Fin n → K} (hx : herm frob x x = 0)
    (hx' : herm frob x' x' = 0) :
    tq (sv α x) * tq (sv α' x') * tq (sv α x) =
      tq (sv (α' + herm frob x x' * α) (x' + herm frob x x' • x)) := by
  rw [tq_mul_tq_mul_tq (isotropic_sv α hx) (isotropic_sv α' hx'), tvU_smul (isotropic_sv α hx),
    herm_sv_sv, smul_sv, sv_add]

theorem isTwin_sv_iff (hn : 1 ≤ n) {α α' : K} {x x' : Fin n → K} (hx0 : x ≠ 0)
    (hx : herm frob x x = 0) (hx0' : x' ≠ 0) (hx' : herm frob x' x' = 0) :
    IsTwin (LocalClass (DG (n + 2)) (tq (v₀ n))) (tq (sv α x)) (tq (sv α' x')) ↔
      ∃ c : K, x' = c • x := by
  have hmem := tq_sv_mem_localClass hn α hx0 hx
  have hmem' := tq_sv_mem_localClass hn α' hx0' hx'
  constructor
  · rintro ⟨-, -, hcomm, hall⟩
    by_contra hne
    simp only [not_exists] at hne
    have hxx' : herm frob x x' = 0 := (tq_sv_commute_iff hn hx0 hx hx0' hx').1 hcomm
    obtain ⟨z, hz, hxz, hx'z⟩ := exists_iso_perp isUnitaryInvolution_frob hx0 hx hx' hxx' hne
    have hz0 : z ≠ 0 := by rintro rfl; exact hx'z (herm_zero_right _ _)
    have h1 := (hall _ (tq_sv_mem_localClass hn 0 hz0 hz)).1
      ((tq_sv_commute_iff hn hz0 hz hx0 hx).2 (herm_eq_zero_comm frob frob_frob hxz))
    exact hx'z (herm_eq_zero_comm frob frob_frob ((tq_sv_commute_iff hn hz0 hz hx0' hx').1 h1))
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; exact hx0' (zero_smul K x)
    refine ⟨hmem, hmem', (tq_sv_commute_iff hn hx0 hx hx0' hx').2
      (by rw [herm_smul_right, hx, mul_zero]), fun q hq => ?_⟩
    obtain ⟨β, y, hy0, hy, rfl⟩ := exists_sv_of_mem_localClass hn hq
    rw [tq_sv_commute_iff hn hy0 hy hx0 hx, tq_sv_commute_iff hn hy0 hy hx0' hx',
      herm_smul_right, mul_eq_zero, or_iff_right hc]

theorem isTwin_add_smul {m : ℕ} (hm : 3 ≤ m) {P Q : Fin m → K} (hP0 : P ≠ 0)
    (hP : herm frob P P = 0) (hQ0 : Q ≠ 0) (hQ : herm frob Q Q = 0) (hPQ : herm frob P Q = 0)
    (hQP : ∀ c : K, Q ≠ c • P) (c : K) :
    IsTwin (LocalClass (DG m) (tq P)) (tq Q) (tq (Q + c • P)) := by
  have hQP' : ∀ c' : K, Q + c • P ≠ c' • P := fun c' h => hQP (c' - c) (by
    rw [sub_smul, ← h, add_sub_cancel_right])
  have hR0 : Q + c • P ≠ 0 := fun h => hQP' 0 (by rw [h, zero_smul])
  have hQP0 : herm frob Q P = 0 := herm_eq_zero_comm frob frob_frob hPQ
  have hR : herm frob (Q + c • P) (Q + c • P) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hP, hQ, hPQ,
      hQP0, mul_zero, add_zero]
  have hPR : herm frob P (Q + c • P) = 0 := by
    rw [herm_add_right, herm_smul_right, hPQ, hP, mul_zero, add_zero]
  refine ⟨(tq_mem_localClass_iff hm hP0 hP hQ0 hQ).2 ⟨hPQ, hQP⟩,
    (tq_mem_localClass_iff hm hP0 hP hR0 hR).2 ⟨hPR, hQP'⟩,
    (tq_commute_iff hm hQ0 hQ hR0 hR).2 (by
      rw [herm_add_right, herm_smul_right, hQ, hQP0, mul_zero, add_zero]), fun z hz => ?_⟩
  obtain ⟨Z, hZ0, hZ, rfl⟩ := hz.1
  have hZP : herm frob Z P = 0 := herm_eq_zero_comm frob frob_frob
    ((tq_mem_localClass_iff hm hP0 hP hZ0 hZ).1 hz).1
  rw [tq_commute_iff hm hZ0 hZ hQ0 hQ, tq_commute_iff hm hZ0 hZ hR0 hR, herm_add_right,
    herm_smul_right, hZP, mul_zero, add_zero]

theorem muY_eq (hn : 1 ≤ n) (y : Fin n → K) :
    muY y = {q | ∃ z : Fin n → K, z ≠ 0 ∧ herm frob z z = 0 ∧ q = tq (sv (herm frob y z) z)} := by
  ext q
  constructor
  · exact exists_wz_of_mem_muY hn
  · rintro ⟨z, hz0, hz, rfl⟩
    exact tq_wz_mem_muY hn y hz0 hz

theorem twinFree_muY (hn : 1 ≤ n) (y : Fin n → K) :
    TwinFree (LocalClass (DG (n + 2)) (tq (v₀ n))) (muY y) := by
  rw [muY_eq hn y]
  rintro _ ⟨z, hz0, hz, rfl⟩ _ ⟨z', hz0', hz', rfl⟩ htw
  obtain ⟨c, rfl⟩ := (isTwin_sv_iff hn hz0 hz hz0' hz').1 htw
  exact (tq_sv_eq_tq_sv_iff hn hz0 hz hz0' hz').2 ⟨c, rfl, by rw [herm_smul_right]⟩

theorem meetsTwins_muY (hn : 1 ≤ n) (y : Fin n → K) :
    MeetsTwins (LocalClass (DG (n + 2)) (tq (v₀ n))) (muY y) := by
  intro a ha
  obtain ⟨α, x, hx0, hx, rfl⟩ := exists_sv_of_mem_localClass hn ha
  rw [muY_eq hn y]
  exact ⟨_, ⟨x, hx0, hx, rfl⟩, (isTwin_sv_iff hn hx0 hx hx0 hx).2 ⟨1, (one_smul K x).symm⟩⟩

theorem exists_muY_eq_muSet (hn : 1 ≤ n) {q : PG (n + 2)} (hq : q ∈ DG (n + 2))
    (hqv : q * tq (v₀ n) ≠ tq (v₀ n) * q) :
    ∃ y : Fin n → K, muSet (DG (n + 2)) (tq (v₀ n)) q = muY y := by
  obtain ⟨u, hu0, hu, rfl⟩ := hq
  have hvu : herm frob (v₀ n) u ≠ 0 := fun h =>
    hqv ((tq_commute_iff (by omega) hu0 hu v₀_ne_zero herm_v₀_v₀).2
      (herm_eq_zero_comm frob frob_frob h))
  set c := (herm frob (v₀ n) u)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hvu
  have htq : tq u = tq (c • u) := (tq_eq_tq_iff (by omega) hu0 hu (smul_ne_zero hc0 hu0)
    (by rw [herm_smul_smul_self hu])).2 ⟨c, rfl⟩
  refine ⟨π n (c • u), ?_⟩
  rw [htq, muSet_eq_muY hn (herm_smul_smul_self hu c)
    (by rw [herm_smul_right, hc, inv_mul_cancel₀ hvu])]

theorem muSections_DG (hn : 2 ≤ n) : MuSections (DG (n + 2)) where
  twinFree p hp q hq hqp := by
    obtain ⟨ψ, hψD, hψp⟩ := Pair.exists_mulEquiv (pair_DG (by omega)) hp
      (tq_mem_DG v₀_ne_zero herm_v₀_v₀)
    have hc := isChart_mulEquiv ψ (LocalClass (DG (n + 2)) p)
    rw [← localClass_congr ψ hψD hψp] at hc
    have hψq : ψ q ∈ DG (n + 2) := hψD ▸ ⟨q, hq, rfl⟩
    have hqv : ψ q * tq (v₀ n) ≠ tq (v₀ n) * ψ q := by
      rw [← hψp, ← map_mul, ← map_mul]
      exact fun h => hqp (ψ.injective h)
    obtain ⟨y, hy⟩ := exists_muY_eq_muSet (by omega) hψq hqv
    refine isChart_twinFree_of_image hc (muSet_subset_localClass p q) ?_
    rw [← muSet_congr ψ hψD, hψp, hy]
    exact twinFree_muY (by omega) y
  meets p hp q hq hqp := by
    obtain ⟨ψ, hψD, hψp⟩ := Pair.exists_mulEquiv (pair_DG (by omega)) hp
      (tq_mem_DG v₀_ne_zero herm_v₀_v₀)
    have hc := isChart_mulEquiv ψ (LocalClass (DG (n + 2)) p)
    rw [← localClass_congr ψ hψD hψp] at hc
    have hψq : ψ q ∈ DG (n + 2) := hψD ▸ ⟨q, hq, rfl⟩
    have hqv : ψ q * tq (v₀ n) ≠ tq (v₀ n) * ψ q := by
      rw [← hψp, ← map_mul, ← map_mul]
      exact fun h => hqp (ψ.injective h)
    obtain ⟨y, hy⟩ := exists_muY_eq_muSet (by omega) hψq hqv
    refine isChart_meetsTwins_of_image hc (muSet_subset_localClass p q) ?_
    rw [← muSet_congr ψ hψD, hψp, hy]
    exact meetsTwins_muY (by omega) y

end CFSG.Fischer.Classification.LocalU
