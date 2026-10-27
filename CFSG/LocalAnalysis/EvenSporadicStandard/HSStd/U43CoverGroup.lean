module

public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Sporadic.SmallOddCore
open scoped commutatorElement

@[expose] def cubeCore {G : Type*} [Group G] (D : Subgroup G) (β : G) : Subgroup G :=
  ⁅D, D⁆ ⊔ closure ((fun a => a ^ 3) '' (D : Set G)) ⊔ zpowers β

theorem cubeCore_le {G : Type*} [Group G] {D : Subgroup G} {β : G} {K : Subgroup G}
    (hc : ∀ a ∈ D, ∀ b ∈ D, ⁅a, b⁆ ∈ K) (hp : ∀ a ∈ D, a ^ 3 ∈ K) (hβ : β ∈ K) :
    cubeCore D β ≤ K :=
  sup_le (sup_le (commutator_le.2 hc) ((closure_le _).2 (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha)))
    (zpowers_le.2 hβ)

theorem commutator_mem_cubeCore {G : Type*} [Group G] {D : Subgroup G} {β a b : G} (ha : a ∈ D)
    (hb : b ∈ D) : ⁅a, b⁆ ∈ cubeCore D β :=
  mem_sup_left (mem_sup_left (commutator_mem_commutator ha hb))

theorem cube_mem_cubeCore {G : Type*} [Group G] {D : Subgroup G} {β a : G} (ha : a ∈ D) :
    a ^ 3 ∈ cubeCore D β :=
  mem_sup_left (mem_sup_right (subset_closure ⟨a, ha, rfl⟩))

theorem self_mem_cubeCore {G : Type*} [Group G] {D : Subgroup G} {β : G} : β ∈ cubeCore D β :=
  mem_sup_right (mem_zpowers β)

theorem map_cubeCore {G G' : Type*} [Group G] [Group G'] (f : G →* G') (D : Subgroup G) (β : G) :
    (cubeCore D β).map f = cubeCore (D.map f) (f β) := by
  have himg : f '' ((fun a : G => a ^ 3) '' (D : Set G)) =
      (fun b : G' => b ^ 3) '' ((D.map f : Subgroup G') : Set G') := by
    rw [coe_map, Set.image_image, Set.image_image]
    simp only [map_pow]
  unfold cubeCore
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_closure,
    MonoidHom.map_zpowers, himg]

section Algebra

theorem conj_commutator_eq {G : Type*} [Group G] {a b b' z z' : G} (h : a * b * a⁻¹ = b * z)
    (h' : a * b' * a⁻¹ = b' * z') (hzb' : Commute z b') (hzz' : Commute z z')
    (hz'b : Commute z' b) : a * ⁅b, b'⁆ * a⁻¹ = ⁅b, b'⁆ := by
  have e0 : a * ⁅b, b'⁆ * a⁻¹ =
      (a * b * a⁻¹) * (a * b' * a⁻¹) * (a * b * a⁻¹)⁻¹ * (a * b' * a⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e0, h, h']
  have e1 : z * b' = b' * z := hzb'.eq
  have e2 : z * z' * z⁻¹ = z' := by rw [hzz'.eq, mul_inv_cancel_right]
  have e3 : z' * b⁻¹ = b⁻¹ * z' := hz'b.inv_right.eq
  calc b * z * (b' * z') * (b * z)⁻¹ * (b' * z')⁻¹
      = b * (z * b') * z' * z⁻¹ * b⁻¹ * z'⁻¹ * b'⁻¹ := by group
    _ = b * (b' * z) * z' * z⁻¹ * b⁻¹ * z'⁻¹ * b'⁻¹ := by rw [e1]
    _ = b * b' * (z * z' * z⁻¹) * b⁻¹ * z'⁻¹ * b'⁻¹ := by group
    _ = b * b' * z' * b⁻¹ * z'⁻¹ * b'⁻¹ := by rw [e2]
    _ = b * b' * (z' * b⁻¹) * z'⁻¹ * b'⁻¹ := by group
    _ = b * b' * (b⁻¹ * z') * z'⁻¹ * b'⁻¹ := by rw [e3]
    _ = ⁅b, b'⁆ := by
      simp only [commutatorElement_def]
      group

theorem conj_pow_eq {G : Type*} [Group G] {a y w : G} (h : a * y * a⁻¹ = y * w)
    (hwa : Commute w a) (n : ℕ) : a ^ n * y * (a ^ n)⁻¹ = y * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : a * w ^ n * a⁻¹ = w ^ n := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ((hwa.pow_left n).symm).eq
    calc a ^ (n + 1) * y * (a ^ (n + 1))⁻¹ = a * (a ^ n * y * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']
          group
      _ = a * (y * w ^ n) * a⁻¹ := by rw [ih]
      _ = (a * y * a⁻¹) * (a * w ^ n * a⁻¹) := by group
      _ = y * w ^ (n + 1) := by rw [h, hw, mul_assoc, ← pow_succ']

variable {T X : Type*} [Group T] [Group X]

theorem twist_mem {κ : T →* X} {E : Subgroup T} [E.Normal] {a c : T} (hc : c ∈ E)
    (hac : κ a * κ c = κ c * κ a) :
    c⁻¹ * (a * c * a⁻¹) ∈ E ∧ κ (c⁻¹ * (a * c * a⁻¹)) = 1 := by
  refine ⟨mul_mem (inv_mem hc) (Normal.conj_mem ‹E.Normal› c hc a), ?_⟩
  simp only [map_mul, map_inv]
  rw [hac]
  group

theorem commute_commutator (κ : T →* X) (E : Subgroup T) [E.Normal]
    (hZ : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) {a b b' : T} (hb : b ∈ E) (hb' : b' ∈ E)
    (hab : κ a * κ b = κ b * κ a) (hab' : κ a * κ b' = κ b' * κ a) :
    a * ⁅b, b'⁆ = ⁅b, b'⁆ * a := by
  obtain ⟨hz, hzk⟩ := twist_mem (κ := κ) (E := E) hb hab
  obtain ⟨hz', hz'k⟩ := twist_mem (κ := κ) (E := E) hb' hab'
  have key := conj_commutator_eq (a := a) (b := b) (b' := b') (z := b⁻¹ * (a * b * a⁻¹))
    (z' := b'⁻¹ * (a * b' * a⁻¹)) (by rw [mul_inv_cancel_left]) (by rw [mul_inv_cancel_left])
    (hZ _ hz hzk b' hb') (hZ _ hz hzk _ hz') (hZ _ hz' hz'k b hb)
  calc a * ⁅b, b'⁆ = a * ⁅b, b'⁆ * a⁻¹ * a := by group
    _ = ⁅b, b'⁆ * a := by rw [key]

theorem commute_cube (κ : T →* X) (E : Subgroup T) [E.Normal]
    (hZ : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) {y e : T} (hy : y ∈ E) (he : e ∈ E)
    (hy3 : y ^ 3 = 1) (hye : κ y * κ e = κ e * κ y) : y * e ^ 3 = e ^ 3 * y := by
  obtain ⟨hw, hwk⟩ := twist_mem (κ := κ) (E := E) hy hye.symm
  have hwe : Commute (y⁻¹ * (e * y * e⁻¹)) e := hZ _ hw hwk e he
  have hwy : Commute (y⁻¹ * (e * y * e⁻¹)) y := hZ _ hw hwk y hy
  have h : e * y * e⁻¹ = y * (y⁻¹ * (e * y * e⁻¹)) := by rw [mul_inv_cancel_left]
  have h3 : (y⁻¹ * (e * y * e⁻¹)) ^ 3 = 1 := by
    have h1 : (y * (y⁻¹ * (e * y * e⁻¹))) ^ 3 = 1 := by
      rw [← h, conj_pow, hy3, mul_one, mul_inv_cancel]
    rw [hwy.symm.mul_pow, hy3, one_mul] at h1
    exact h1
  have h4 := conj_pow_eq h hwe 3
  rw [h3, mul_one] at h4
  calc y * e ^ 3 = (e ^ 3 * y * (e ^ 3)⁻¹) * e ^ 3 := by rw [h4]
    _ = e ^ 3 * y := by group

theorem ker_commute_of_perfect (κ : T →* X) (E : Subgroup T) [E.Normal] (hE : ⁅E, E⁆ = E)
    (hZ : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) {a : T} (ha : κ a = 1) {b : T}
    (hb : b ∈ E) : a * b = b * a := by
  have hcomm : ⁅E, E⁆ ≤ centralizer ({a} : Set T) := by
    rw [commutator_le]
    intro b hb b' hb'
    rw [mem_centralizer_singleton_iff]
    exact (commute_commutator κ E hZ hb hb' (by rw [ha, one_mul, mul_one])
      (by rw [ha, one_mul, mul_one])).symm
  rw [hE] at hcomm
  exact (mem_centralizer_singleton_iff.1 (hcomm hb)).symm

end Algebra

section Orbit

variable {T X : Type*} [Group T] [Group X]

theorem cubeCore_le_map (κ : T →* X) (E : Subgroup T) [E.Normal]
    (hZ : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) {y : T} (hyE : y ∈ E) (hy3 : y ^ 3 = 1) :
    cubeCore (E.map κ ⊓ centralizer ({κ y} : Set X)) (κ y) ≤
      (E ⊓ centralizer ({y} : Set T)).map κ := by
  refine cubeCore_le ?_ ?_ ?_
  · intro a ha b hb
    obtain ⟨⟨ea, hea, rfl⟩, hac⟩ := mem_inf.1 ha
    obtain ⟨⟨eb, heb, rfl⟩, hbc⟩ := mem_inf.1 hb
    refine ⟨⁅ea, eb⁆, mem_inf.2 ⟨?_, ?_⟩, map_commutatorElement κ ea eb⟩
    · simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hea heb) (inv_mem hea)) (inv_mem heb)
    · rw [mem_centralizer_singleton_iff]
      exact (commute_commutator κ E hZ hea heb (mem_centralizer_singleton_iff.1 hac).symm
        (mem_centralizer_singleton_iff.1 hbc).symm).symm
  · intro a ha
    obtain ⟨⟨ea, hea, rfl⟩, hac⟩ := mem_inf.1 ha
    refine ⟨ea ^ 3, mem_inf.2 ⟨pow_mem hea 3, ?_⟩, map_pow κ ea 3⟩
    rw [mem_centralizer_singleton_iff]
    exact (commute_cube κ E hZ hyE hea hy3 (mem_centralizer_singleton_iff.1 hac).symm).symm
  · exact ⟨y, mem_inf.2 ⟨hyE, mem_centralizer_singleton_iff.2 rfl⟩, rfl⟩

theorem orbit_mul_card_le [Finite T] [Finite X] (κ : T →* X) (hκ : Function.Surjective κ)
    (E : Subgroup T) [E.Normal] (hE : ⁅E, E⁆ = E)
    (hZ : ∀ a ∈ E, κ a = 1 → ∀ b ∈ E, a * b = b * a) {y : T} (hyE : y ∈ E) (hy3 : y ^ 3 = 1) :
    {w : T | ∃ g : T, κ g ∈ centralizer ({κ y} : Set X) ∧ w = g * y * g⁻¹}.ncard *
      Nat.card ↥(cubeCore (E.map κ ⊓ centralizer ({κ y} : Set X)) (κ y)) ≤
      Nat.card ↥(centralizer ({κ y} : Set X)) := by
  set C : Subgroup X := centralizer ({κ y} : Set X) with hCdef
  set K : Subgroup X := cubeCore (E.map κ ⊓ C) (κ y) with hKdef
  set L : Subgroup X := (E ⊓ centralizer ({y} : Set T)).map κ with hLdef
  have hKL : K ≤ L := cubeCore_le_map κ E hZ hyE hy3
  have hLC : L ≤ C := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨-, hec⟩ := mem_inf.1 he
    rw [mem_centralizer_singleton_iff] at hec
    rw [hCdef, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hec]
  have hcomap : K.comap κ ≤ centralizer ({y} : Set T) := by
    intro g hg
    obtain ⟨e, he, hegg⟩ := hKL (mem_comap.1 hg)
    obtain ⟨heE, hec⟩ := mem_inf.1 he
    have ha : κ (e⁻¹ * g) = 1 := by rw [map_mul, map_inv, hegg, inv_mul_cancel]
    have hy' := ker_commute_of_perfect κ E hE hZ ha hyE
    rw [mem_centralizer_singleton_iff] at hec ⊢
    calc g * y = e * ((e⁻¹ * g) * y) := by group
      _ = e * (y * (e⁻¹ * g)) := by rw [hy']
      _ = (e * y) * (e⁻¹ * g) := by group
      _ = (y * e) * (e⁻¹ * g) := by rw [hec]
      _ = y * g := by group
  set G : Subgroup T := C.comap κ with hGdef
  have horbit : {w : T | ∃ g : T, κ g ∈ C ∧ w = g * y * g⁻¹} = conjClass G y := by
    ext w
    simp only [Set.mem_ofPred_eq, conjClass, hGdef, mem_comap]
  rw [horbit]
  have h1 := ncard_conjClass_mul_card G y
  have h2 := relIndex_mul_card (centralizer ({y} : Set T)) G
  rw [inf_comm] at h2
  have hpos : 0 < Nat.card ↥(G ⊓ centralizer ({y} : Set T)) := Nat.card_pos
  have h3 : (conjClass G y).ncard = (centralizer ({y} : Set T)).relIndex G :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have h4 : (centralizer ({y} : Set T)).relIndex G ∣ (K.comap κ).relIndex G :=
    relIndex_dvd_of_le_left G hcomap
  have h5 : (K.comap κ).relIndex G = K.relIndex C := by
    rw [hGdef, relIndex_comap, map_comap_eq_self_of_surjective hκ]
  have h6 := relIndex_mul_card K C
  rw [inf_eq_left.2 (hKL.trans hLC)] at h6
  have hrel : 0 < K.relIndex C := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, zero_mul] at h6
    exact (Nat.card_pos (α := ↥C)).ne' h6.symm
  rw [h3]
  calc (centralizer ({y} : Set T)).relIndex G * Nat.card ↥K
      ≤ K.relIndex C * Nat.card ↥K :=
        Nat.mul_le_mul_right _ (Nat.le_of_dvd hrel (h5 ▸ h4))
    _ = Nat.card ↥C := h6

end Orbit

end CFSG.EvenSporadicStandard.HSStd.U43
