module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.PSp45Embed
public import Certificates.Certificate27232
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Step1

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS

theorem natCard_mem_list_of_nodup {α : Type*} [DecidableEq α] (l : List α) (hnd : l.Nodup) :
    Nat.card {a // a ∈ l} = l.length := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (List.mem_toFinset (l := l)).symm)),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem card_centralizer_tau1_ge :
    960 ≤ Nat.card ↥(centralizer ({mkPG pgTau1 pgTau1_so} : Set PGSp45)) := by
  have hco : PGCore := Certificates.certificate27232.toMatrix
  have hCso : ∀ A ∈ pgCList, IsSO5 A := fun A hA => (hco.cent A hA).1
  let f : {A : SoMat5 // A ∈ pgCList} → ↥(centralizer ({mkPG pgTau1 pgTau1_so} : Set PGSp45)) :=
    fun A => ⟨mkPG A.1 (hCso A.1 A.2), by
      rw [mem_centralizer_singleton_iff]
      exact pg_ext (hco.cent A.1 A.2).2⟩
  have hinj : Function.Injective f := by
    intro A B hAB
    apply Subtype.ext
    have := congrArg (fun z : ↥(centralizer ({mkPG pgTau1 pgTau1_so} : Set PGSp45)) =>
      z.1.1.1) hAB
    simpa [f] using this
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [natCard_mem_list_of_nodup _ hco.ndC, hco.lenC] at h1

theorem card_centralizer_ge_of_conj_tau1 {y g : PGSp45}
    (hg : g * y * g⁻¹ = mkPG pgTau1 pgTau1_so) :
    960 ≤ Nat.card ↥(centralizer ({y} : Set PGSp45)) := by
  rw [← card_centralizer_map (MulAut.conj g) y]
  have : (MulAut.conj g) y = mkPG pgTau1 pgTau1_so := by simpa [MulAut.conj_apply] using hg
  rw [this]
  exact card_centralizer_tau1_ge

theorem exists_conj_rep_matrix (hc : PGStage1)
    (hsyl : Nat.card (pgP0 hc) = 2 ^ (Nat.card PGSp45).factorization 2)
    {t : PGSp45} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ (g : PGSp45) (i : Fin 4), g * t * g⁻¹ = mkPG (pgReps i) (hc.reps i).1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g0, hg0⟩ := exists_conj_mem_sylow (Sylow.ofCard (pgP0 hc) hsyl) rfl ht
  set t' := g0⁻¹ * t * g0 with ht'
  have ht'1 : t' * t' = 1 := by
    rw [ht']
    calc g0⁻¹ * t * g0 * (g0⁻¹ * t * g0) = g0⁻¹ * (t * t) * g0 := by group
      _ = 1 := by rw [ht]; group
  have ht'ne : t' ≠ 1 := by
    intro h1
    apply ht1
    have : t = g0 * t' * g0⁻¹ := by rw [ht']; group
    rw [this, h1]
    group
  have hA : t'.1.1 ∈ pgP0List := (mem_pgP0 hc).1 hg0
  have hAA : t'.1.1 * t'.1.1 = 1 := by
    rw [← pg_mul_val, ht'1, pg_one_val]
  rcases hc.invols _ hA hAA with h1 | ⟨e, he, he1⟩
  · exact absurd (pg_ext (by rw [h1, pg_one_val])) ht'ne
  · obtain ⟨-, hso, hmat⟩ := hc.table e he
    set h := mkPG e.2.1 hso with hh
    have hconj : h * t' * h⁻¹ = mkPG (pgReps e.2.2) (hc.reps e.2.2).1 := by
      apply conj_eq_of_mat
      have h2 := hmat
      rw [he1] at h2
      exact h2
    refine ⟨h * g0⁻¹, e.2.2, ?_⟩
    rw [← hconj, ht']
    group

namespace PGSp45Emb

variable {G : Type} [Group G] [Finite G] {ψ : G →* PGSp45} (h : PGSp45Emb ψ)

include h

theorem exists_conj_tau1 {u : G} (hu : orderOf u = 2)
    (hno15 : ∀ c ∈ centralizer ({u} : Set G), c ^ 15 = 1 → c ^ 3 = 1 ∨ c ^ 5 = 1)
    (h13 : ¬ 13 ∣ Nat.card ↥(centralizer ({u} : Set G)))
    (h64 : ¬ 64 ∣ Nat.card ↥(centralizer ({u} : Set G))) :
    ∃ g : PGSp45, g * ψ u * g⁻¹ = mkPG pgTau1 pgTau1_so := by
  have hc : PGStage1 := Certificates.certificate27230.toMatrix
  have hsyl : Nat.card (pgP0 hc) = 2 ^ (Nat.card PGSp45).factorization 2 := by
    rw [card_pgP0, h.card, factorization_two_card_pgsp45]
    norm_num
  have hy2 : ψ u * ψ u = 1 := by
    rw [← map_mul, mul_self_eq_one_of_orderOf_eq_two hu, map_one]
  have hy1 : ψ u ≠ 1 := by
    intro h1
    have : u = 1 := h.inj (h1.trans (map_one ψ).symm)
    rw [this, orderOf_one] at hu
    omega
  obtain ⟨g, i, hgi⟩ := exists_conj_rep_matrix hc hsyl hy2 hy1
  have key : ∀ {z : PGSp45}, z * mkPG (pgReps i) (hc.reps i).1 =
      mkPG (pgReps i) (hc.reps i).1 * z →
      (g⁻¹ * z * g) * ψ u = ψ u * (g⁻¹ * z * g) := by
    intro z hz
    rw [← hgi] at hz
    calc g⁻¹ * z * g * ψ u = g⁻¹ * (z * (g * ψ u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * ψ u * g⁻¹) * z) * g := by rw [hz]
      _ = ψ u * (g⁻¹ * z * g) := by group
  have hpow : ∀ (A : SoMat5) (hA : IsSO5 A) (n : ℕ),
      (g⁻¹ * mkPG A hA * g) ^ n = 1 ↔ A ^ n = 1 := by
    intro A hA n
    rw [conj_inv_pow, show g⁻¹ * mkPG A hA ^ n * g = g⁻¹ * mkPG A hA ^ n * (g⁻¹)⁻¹ by
        rw [inv_inv], conj_eq_one_iff, pg_eq_one_iff, pg_pow_val, mkPG_val]
  refine ⟨g, ?_⟩
  fin_cases i
  ·
    exact hgi
  ·
    exfalso
    obtain ⟨hso, hcomm, h15, h3, h5⟩ := hc.x15
    have hxc : mkPG pgX15 hso * mkPG (pgReps 1) (hc.reps 1).1 =
        mkPG (pgReps 1) (hc.reps 1).1 * mkPG pgX15 hso := pg_ext hcomm
    obtain ⟨w, hwC, hw⟩ := h.exists_cent_of_odd (u := u) (z := g⁻¹ * mkPG pgX15 hso * g)
      (m := 15) (by decide) ((hpow _ hso 15).2 h15) (key hxc)
    have hw15 : w ^ 15 = 1 :=
      h.inj (by rw [map_pow, hw, map_one]; exact (hpow _ hso 15).2 h15)
    rcases hno15 w hwC hw15 with h' | h'
    · exact h3 ((hpow _ hso 3).1 (by rw [← hw, ← map_pow, h', map_one]))
    · exact h5 ((hpow _ hso 5).1 (by rw [← hw, ← map_pow, h', map_one]))
  ·
    exfalso
    let K : Subgroup PGSp45 := (pgP0 hc).map (MulAut.conj g⁻¹).toMonoidHom
    have hK : Nat.card K = 128 := by
      rw [show Nat.card K = Nat.card (pgP0 hc) from
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_pgP0]
    have hKC : K ≤ centralizer ({ψ u} : Set PGSp45) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hpc : p * mkPG (pgReps 2) (hc.reps 2).1 = mkPG (pgReps 2) (hc.reps 2).1 * p := by
        apply pg_ext
        exact hc.tau3 _ ((mem_pgP0 hc).1 hp)
      have hgi' : g * ψ u * g⁻¹ = mkPG (pgReps 2) (hc.reps 2).1 := hgi
      rw [← hgi'] at hpc
      show g⁻¹ * p * g⁻¹⁻¹ * ψ u = ψ u * (g⁻¹ * p * g⁻¹⁻¹)
      calc g⁻¹ * p * g⁻¹⁻¹ * ψ u = g⁻¹ * (p * (g * ψ u * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * ψ u * g⁻¹) * p) * g := by rw [hpc]
        _ = ψ u * (g⁻¹ * p * g⁻¹⁻¹) := by group
    have hdvd := h.card_inf_dvd u K hKC
    have hge := h.card_le_two_mul K
    rw [hK] at hge
    have hd128 : Nat.card ↥(ψ.range ⊓ K) ∣ 2 ^ 7 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : ψ.range ⊓ K ≤ K)
      rwa [hK] at this
    obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd128
    have hj6 : 6 ≤ j := by
      by_contra hj6
      have hj5 : j ≤ 5 := by omega
      have : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hj5
      omega
    apply h64
    have : 64 ∣ Nat.card ↥(ψ.range ⊓ K) := by
      rw [hcj]
      exact (pow_dvd_pow 2 hj6 : 2 ^ 6 ∣ 2 ^ j)
    exact this.trans hdvd
  ·
    exfalso
    obtain ⟨hso, hcomm, h13', hne⟩ := hc.x13
    have hxc : mkPG pgX13 hso * mkPG (pgReps 3) (hc.reps 3).1 =
        mkPG (pgReps 3) (hc.reps 3).1 * mkPG pgX13 hso := pg_ext hcomm
    obtain ⟨w, hwC, hw⟩ := h.exists_cent_of_odd (u := u) (z := g⁻¹ * mkPG pgX13 hso * g)
      (m := 13) (by decide) ((hpow _ hso 13).2 h13') (key hxc)
    have hw13 : w ^ 13 = 1 :=
      h.inj (by rw [map_pow, hw, map_one]; exact (hpow _ hso 13).2 h13')
    have hw1 : w ≠ 1 := by
      intro h1
      apply hne
      have := (hpow _ hso 1).1 (by rw [pow_one, ← hw, h1, map_one])
      simpa using this
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have hord : orderOf w = 13 := orderOf_eq_prime hw13 hw1
    apply h13
    have : orderOf (⟨w, hwC⟩ : ↥(centralizer ({u} : Set G))) = 13 := by
      rw [Subgroup.orderOf_mk]
      exact hord
    rw [← this]
    exact orderOf_dvd_natCard _

end PGSp45Emb

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
