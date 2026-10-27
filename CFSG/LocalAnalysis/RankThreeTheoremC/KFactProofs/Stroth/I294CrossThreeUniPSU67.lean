module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeUniPSU4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

theorem i294CrossModelPSU67_holds : I294CrossModelPSU67 := by
  intro q K _ _ hK h3q h3q1 n hn x hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨r, f, hr, hchar, rfl⟩ := CrossUni.exists_prime_pow_of_card_sq hK
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  obtain ⟨g, hg3, rfl⟩ := exists_lift_pow_three (H := StatedSU n (r ^ f) K) (N := r ^ f + 1)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q1)
    (fun z hz => (CrossUni.statedSU_scalar_pow hr hK hn1 z hz).2) hx3
  have hσ : IsUnitaryInvolution (unitaryInvolution K r f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hq : 1 < r ^ f := one_lt_pow_of_card hK
  obtain ⟨m, hm⟩ : ∃ m, r ^ f = 3 * m + 1 := ⟨(r ^ f) / 3, by omega⟩
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
    exact Dvd.dvd.mul_left (by omega) _
  obtain ⟨ζ, hζ⟩ := CrossUni.exists_isPrimitiveRoot_three hcard
  have hσζ : unitaryInvolution K r f ζ = ζ := by
    rw [unitaryInvolution_apply, hm, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hnorm : ∀ c : K, c ^ 3 = 1 → unitaryInvolution K r f c * c = 1 → c = 1 := by
    intro c hc3 hcq
    rw [unitaryInvolution_apply, ← pow_succ] at hcq
    have h1 := pow_gcd_eq_one.2 ⟨hc3, hcq⟩
    rwa [((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3q1).gcd_eq_one, pow_one] at h1
  have hgS : (g : GL (Fin n) K) ∈ SUid (unitaryInvolution K r f) n := by
    rw [SUid_eq_statedSU hK n]
    exact g.2
  have hsiso := (mem_SUid.1 hgS).2
  have hs : (g : GL (Fin n) K) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hg3
  have hspow : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hs
    simpa using this
  have hSp : (Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ 3 = 1 := by
    rw [← Matrix.toLin'_pow, hspow, Matrix.toLin'_one]
    rfl
  have hS : ∀ x y, herm (unitaryInvolution K r f)
      (Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x)
      (Matrix.toLin' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) y) =
      herm (unitaryInvolution K r f) x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_mulVec, hsiso, Matrix.one_mulVec]
  obtain ⟨u, w, hpairs⟩ := CrossUni.exists_hypPairs hσ hζ hσζ hSp hS 3 (by omega)
  obtain ⟨F, hFi, hFc, hFs⟩ := CrossUni.exists_torusHom_pairs hσ.invol hζ hnorm
    (g : GL (Fin n) K) hsiso hs hpairs
  have hA : Nat.card (Fin 3 → Multiplicative (ZMod 3)) = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  exact le_pRank_centralizer_statedProj (H := StatedSU n (r ^ f) K)
    (A := Fin 3 → Multiplicative (ZMod 3)) (k := 3) (fun a b => mul_comm a b)
    (fun a => funext fun i => CrossUni.pow_prime_eq_one_zmod (a i)) hA
    ((SUid (unitaryInvolution K r f) n).subtype.comp F)
    ((SUid (unitaryInvolution K r f) n).subtype_injective.comp hFi)
    (fun a => by
      rw [← SUid_eq_statedSU hK n]
      exact (F a).2)
    (fun a ha => hFi (by rw [hFs a ha, map_one])) g
    (fun a => hFc a)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
