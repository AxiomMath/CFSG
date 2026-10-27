module

public import CFSG.HardMathSupport.Foote.E27.SporSylow
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

theorem eightyOne_dvd_card_of_isPGroup {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    (hH : IsPGroup 3 H) (h81 : 81 ≤ Nat.card H) : 81 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn] at h81 ⊢
  have hn4 : 4 ≤ n := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  exact (show 81 = 3 ^ 4 by norm_num) ▸ Nat.pow_dvd_pow 3 hn4

theorem card_centralizer_map_equiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (x : G) :
    Nat.card (centralizer ({φ x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  refine Nat.card_congr (φ.symm.toEquiv.subtypeEquiv fun y => ?_)
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  show _ ↔ φ.symm y * x = x * φ.symm y
  rw [← φ.injective.eq_iff, map_mul, map_mul, MulEquiv.apply_symm_apply]

section Kill

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_centralizer_kill (h : E27Config X K R T z) (hz : z ∈ K)
    {J : Type*} [Group J] [Finite J] (φ : ↥K ≃* J) (Q : Subgroup J)
    (hQ : Nat.card Q = 3 ^ (Nat.card J).factorization 3)
    (hkill : ∀ s ∈ Q, s ^ 3 = 1 → s ≠ 1 → 81 ∣ Nat.card (centralizer ({s} : Set J))) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q' : Subgroup ↥K := Q.comap φ.toMonoidHom with hQ'def
  have hcardQ' : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (φ.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have hcardK : Nat.card ↥K = Nat.card J := Nat.card_congr φ.toEquiv
  let S₀ : Sylow 3 ↥K := Sylow.ofCard Q' (by rw [hcardQ', hQ, hcardK])
  obtain ⟨z₀, hz₀S, hord, -, -, hn81⟩ := h.exists_conj_mem_sylow hz S₀
  apply hn81
  have hmem : φ z₀ ∈ Q := hz₀S
  have h3 : φ z₀ ^ 3 = 1 := by rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have h1 : φ z₀ ≠ 1 := by
    intro h1
    have h0 : z₀ = 1 := φ.injective (h1.trans (map_one φ).symm)
    rw [h0, orderOf_one] at hord
    norm_num at hord
  have h81 := hkill (φ z₀) hmem h3 h1
  rwa [card_centralizer_map_equiv] at h81

end Kill

section Cover

variable {W : Type*} [Group W]

theorem dvd81_card_centralizer_of_e81_cover {J Q : Subgroup W} [Finite J] {z : W} {n : ℕ}
    (hQJ : Q ≤ J) (hQ : Nat.card Q = 3 ^ n) (hn : 4 ≤ n) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hgood : ∀ s ∈ Q, s ^ 3 = 1 → s ∉ zpowers z →
      ∃ E : Subgroup W, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧
        z ∈ E) :
    ∀ s ∈ Q.subgroupOf J, s ^ 3 = 1 → s ≠ 1 → 81 ∣ Nat.card (centralizer ({s} : Set ↥J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hs hs3 _
  have hsQ : (s : W) ∈ Q := mem_subgroupOf.mp hs
  have key : ∀ H : Subgroup W, H ≤ J → (∀ h ∈ H, h * (s : W) = (s : W) * h) →
      81 ∣ Nat.card H → 81 ∣ Nat.card (centralizer ({s} : Set ↥J)) := by
    intro H hHJ hHc h81
    have hle : H.subgroupOf J ≤ centralizer ({s} : Set ↥J) := fun h hh => by
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (hHc h (mem_subgroupOf.mp hh))
    have hcard : Nat.card (H.subgroupOf J) = Nat.card H :=
      Nat.card_congr (subgroupOfEquivOfLe hHJ).toEquiv
    exact h81.trans (hcard ▸ card_dvd_of_le hle)
  by_cases hsz : (s : W) ∈ zpowers z
  ·
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hsz
    refine key Q hQJ (fun q hq => ?_) ?_
    · rw [← hk]
      exact ((Commute.zpow_right (hzc q hq) k))
    · rw [hQ]
      exact (show 81 = 3 ^ 4 by norm_num) ▸ Nat.pow_dvd_pow 3 hn
  · obtain ⟨E, hEJ, hE, hE81, hsE, -⟩ := hgood s hsQ (by simpa using congrArg Subtype.val hs3)
      hsz
    have : Finite E := Finite.of_injective (fun x : E => (⟨x, hEJ x.2⟩ : J))
      fun x y hxy => Subtype.ext (congrArg (fun u : ↥J => (u : W)) hxy)
    refine key E hEJ (fun e he => ?_) ?_
    · exact congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨s, hsE⟩)
    · refine eightyOne_dvd_card_of_isPGroup (fun x => ⟨1, ?_⟩) hE81
      rw [pow_one]
      exact Subtype.ext (hE.2 x x.2)

end Cover

section CoverKill

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} {W : Type*} [Group W]

theorem E27Config.false_of_e81_cover (h : E27Config X K R T z) (hz : z ∈ K) {J Q : Subgroup W}
    [Finite J] (φ : ↥K ≃* ↥J) {z' : W} (hQJ : Q ≤ J)
    (hQ : Nat.card Q = 3 ^ (Nat.card J).factorization 3) (h4 : 4 ≤ (Nat.card J).factorization 3)
    (hzc : ∀ q ∈ Q, q * z' = z' * q)
    (hgood : ∀ s ∈ Q, s ^ 3 = 1 → s ∉ zpowers z' →
      ∃ E : Subgroup W, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧ s ∈ E ∧
        z' ∈ E) :
    False := by
  refine h.false_of_centralizer_kill hz φ (Q.subgroupOf J) ?_
    (dvd81_card_centralizer_of_e81_cover hQJ hQ h4 hzc hgood)
  rw [← hQ]
  exact Nat.card_congr (subgroupOfEquivOfLe hQJ).toEquiv

end CoverKill

end CFSG.HardMathSupport.Foote.E27
