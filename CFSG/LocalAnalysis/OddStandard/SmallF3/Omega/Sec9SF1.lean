module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec9f_card_stab {N : Subgroup G} {X : Set G} (hX : ConjTwoTransOn N X) {t : G}
    (ht : t ∈ X) (h2 : 2 ≤ X.ncard) :
    Nat.card ↥N = X.ncard * Nat.card ↥(N ⊓ centralizer ({t} : Set G)) := by
  letI : MulAction ↥N G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have hsmul : ∀ (n : ↥N) (x : G), n • x = (n : G) * x * (n : G)⁻¹ :=
    fun n x => ConjAct.toConjAct_smul (N.subtype n) x
  have horbit : MulAction.orbit ↥N t = X := by
    ext a
    constructor
    · rintro ⟨n, rfl⟩
      change n • t ∈ X
      rw [hsmul]
      exact hX.1 n n.2 t ht
    · intro ha
      obtain ⟨b, hbX, hbt⟩ := Set.exists_ne_of_one_lt_ncard h2 t
      obtain ⟨d, hdX, hda⟩ := Set.exists_ne_of_one_lt_ncard h2 a
      obtain ⟨n, hn, hna, -⟩ := hX.2 t ht b hbX a ha d hdX hbt.symm hda.symm
      exact ⟨⟨n, hn⟩, by change (⟨n, hn⟩ : ↥N) • t = a; rw [hsmul]; exact hna⟩
  have hstab : MulAction.stabilizer ↥N t = (N ⊓ centralizer ({t} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, hsmul]
    exact ⟨fun h => ⟨n.2, mul_inv_eq_iff_eq_mul.mp h⟩,
      fun h => by rw [h.2, mul_inv_cancel_right]⟩
  have hstab_card : Nat.card (MulAction.stabilizer ↥N t) =
      Nat.card ↥(N ⊓ centralizer ({t} : Set G)) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmain := Subgroup.card_mul_index (H := MulAction.stabilizer ↥N t)
  rw [MulAction.index_stabilizer, horbit, hstab_card, mul_comm] at hmain
  exact hmain.symm

theorem sec9f_count_contra {Γ N : Type} [Group Γ] [Finite Γ] [Group N] [Finite N] (ρ : N →* Γ)
    (Nt : Subgroup N) (hker : ρ.ker ≤ Nt) (hidx : Nt.index = 16) (Ht : Subgroup Γ)
    (hHt : Ht ≤ Nt.map ρ) (h360 : 360 ∣ Nat.card Ht) (hΓ : Nat.card Γ = 20160) : False := by
  have hsup : Nt ⊔ ρ.ker = Nt := sup_eq_left.2 hker
  have hidxmap : (Nt.map ρ).index = 16 * ρ.range.index := by
    rw [Subgroup.index_map, hsup, hidx]
  have hcardNt := Subgroup.card_mul_index (H := Nt.map ρ)
  have hcardR := Subgroup.card_mul_index (H := ρ.range)
  rw [hidxmap, hΓ] at hcardNt
  rw [hΓ] at hcardR
  have hi : ρ.range.index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcardR
    exact absurd hcardR (by norm_num)
  have hcard_eq : Nat.card ρ.range = 16 * Nat.card (Nt.map ρ) := by
    refine Nat.mul_right_cancel (Nat.pos_of_ne_zero hi) ?_
    rw [hcardR, ← hcardNt]
    ring
  have h360' : 360 ∣ Nat.card (Nt.map ρ) := h360.trans (Subgroup.card_dvd_of_le hHt)
  have h5760 : 5760 ∣ Nat.card ρ.range := by
    rw [hcard_eq]
    have hsplit : (5760 : ℕ) = 16 * 360 := by norm_num
    rw [hsplit]
    exact Nat.mul_dvd_mul_left 16 h360'
  have hdvdΓ : Nat.card ρ.range ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card ρ.range
  exact absurd (hΓ ▸ h5760.trans hdvdΓ) (by norm_num)

theorem sec9f_sylow_sup {C K0 E : Subgroup G} (hE : IsSylow2Of E C) (hK : K0 ≤ C)
    (hidx : ∃ k : ℕ, K0.relIndex C = 2 ^ k) : E ⊔ K0 = C := by
  obtain ⟨hEC, -, hEodd⟩ := hE
  obtain ⟨k, hk⟩ := hidx
  have hDle : E ⊔ K0 ≤ C := sup_le hEC hK
  have hdvdE : (E ⊔ K0).relIndex C ∣ E.relIndex C :=
    Subgroup.relIndex_dvd_of_le_left (H := E) (K := E ⊔ K0) (L := C) le_sup_left
  have hdvdK : (E ⊔ K0).relIndex C ∣ K0.relIndex C :=
    Subgroup.relIndex_dvd_of_le_left (H := K0) (K := E ⊔ K0) (L := C) le_sup_right
  rw [hk] at hdvdK
  have hodd : Odd ((E ⊔ K0).relIndex C) :=
    Nat.not_even_iff_odd.mp fun he => hEodd ((he.trans_dvd hdvdE).two_dvd)
  have hn1 : (E ⊔ K0).relIndex C = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk
      have hCK : C ≤ K0 := (Subgroup.relIndex_eq_one).1 hk
      exact (Subgroup.relIndex_eq_one).2 (hCK.trans le_sup_right)
    · exact Nat.eq_one_of_dvd_coprimes
        ((Nat.coprime_pow_right_iff hkpos _ 2).2 hodd.coprime_two_right) (dvd_refl _) hdvdK
  exact le_antisymm hDle ((Subgroup.relIndex_eq_one).1 hn1)

private lemma mem_sup_of_conj_mem {O A : Subgroup G}
    (hAO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) {x : G} (hx : x ∈ O ⊔ A) :
    ∃ o ∈ O, ∃ a ∈ A, o * a = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, A.one_mem, by simp⟩
    · exact ⟨1, O.one_mem, x, hx, by simp⟩
  · exact ⟨1, O.one_mem, 1, A.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * (z₁ * y₂ * z₁⁻¹), O.mul_mem hy₁ (hAO z₁ hz₁ y₂ hy₂),
      z₁ * z₂, A.mul_mem hz₁ hz₂, ?_⟩
    group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨z⁻¹ * y⁻¹ * z, ?_, z⁻¹, A.inv_mem hz, by group⟩
    have h := hAO z⁻¹ (A.inv_mem hz) y⁻¹ (O.inv_mem hy)
    simpa using h

theorem sec9f_inf_eq {E A O : Subgroup G} (hE : IsPGroup 2 E) (hAE : A ≤ E)
    (hO : Odd (Nat.card O)) (hAO : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O) :
    E ⊓ (O ⊔ A) = A := by
  refine le_antisymm ?_ (le_inf hAE le_sup_right)
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxE, hxOA⟩ := hx
  obtain ⟨o, hoO, a, haA, rfl⟩ := mem_sup_of_conj_mem hAO hxOA
  have hoE : o ∈ E := by
    have h : o = o * a * a⁻¹ := by group
    rw [h]
    exact E.mul_mem hxE (E.inv_mem (hAE haA))
  have hdvd : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hoO
  have hodd : Odd (orderOf o) :=
    Nat.not_even_iff_odd.mp fun he => hO.not_two_dvd_nat (he.two_dvd.trans hdvd)
  obtain ⟨k, hk⟩ := hE.exists_orderOf_dvd_pow (⟨o, hoE⟩ : ↥E)
  rw [Subgroup.orderOf_mk] at hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk
  have hj0 : j = 0 := by
    by_contra hjne
    have h2odd : Odd 2 := (Nat.odd_pow_iff hjne).1 (hj ▸ hodd)
    exact (by decide : ¬ Odd 2) h2odd
  have ho1 : o = 1 := by
    rw [← orderOf_eq_one_iff, hj, hj0, pow_zero]
  rw [ho1, one_mul]
  exact haA

theorem sec9f_map_eq_range {X Y : Type} [Group X] [Group Y] (f : X →* Y) (E : Subgroup X)
    (h : E ⊔ f.ker = ⊤) : E.map f = f.range := by
  have h' := congrArg (Subgroup.map f) h
  rw [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq, ← MonoidHom.range_eq_map] at h'
  exact h'

end CFSG.OddStandard.SmallF3.Omega
