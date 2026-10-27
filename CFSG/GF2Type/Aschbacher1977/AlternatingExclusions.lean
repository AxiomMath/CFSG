module

public import CFSG.LargeExtraspecial.S3Basic
import CFSG.GF2Type.Aschbacher1977.SmallExclusions
import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
import CFSG.LargeExtraspecial.AS35COdd
import CFSG.LargeExtraspecial.AS35DQ
import CFSG.LargeExtraspecial.AS35WAlt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.LargeExtraspecial Subgroup Equiv Equiv.Perm CFSG.GH74.GLS.Layer3

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_dvd_card_M (S : Setting G) {k : ℕ} (hk : 2 ^ k ∣ Nat.card G) :
    2 ^ k ∣ Nat.card S.M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -, hPM⟩ := S.exists_sylow_le_M
  have hv : k ≤ (Nat.card G).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hk
  have h2 : 2 ^ k ∣ Nat.card P := by
    rw [Sylow.card_eq_multiplicity P]
    exact pow_dvd_pow 2 hv
  exact h2.trans (Subgroup.card_dvd_of_le hPM)

theorem eq_bot_of_odd_normal_centralizer_of_mulEquiv (S : Setting G) {H : Type} [Group H]
    (e : G ≃* H) {N : Subgroup H} (hNC : N ≤ centralizer ({e S.z} : Set H))
    (hNn : ∀ c ∈ centralizer ({e S.z} : Set H), ∀ k ∈ N, c * k * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  let N' : Subgroup G := N.comap e.toMonoidHom
  have hN'C : N' ≤ centralizer ({S.z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxN : e x ∈ N := by
      rwa [Subgroup.mem_comap] at hx
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hNC hxN)
  have hN'n : ∀ c ∈ centralizer ({S.z} : Set G), ∀ x ∈ N', c * x * c⁻¹ ∈ N' := by
    intro c hc x hx
    change e (c * x * c⁻¹) ∈ N
    have hxN : e x ∈ N := by
      rwa [Subgroup.mem_comap] at hx
    have hcN : e c ∈ centralizer ({e S.z} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc]
    simpa only [map_mul, map_inv] using hNn (e c) hcN (e x) hxN
  have hcard : Nat.card N' = Nat.card N := by
    change Nat.card (N.comap e.toMonoidHom) = Nat.card N
    rw [Subgroup.comap_equiv_eq_map_symm' e N]
    exact Subgroup.card_map_of_injective (K := N) (f := e.symm.toMonoidHom) e.symm.injective
  have hodd' : Odd (Nat.card N') := by rw [hcard]; exact hodd
  rw [eq_bot_iff_forall]
  intro k hk
  have haN' : e.symm k ∈ N' := by
    change e (e.symm k) ∈ N
    simpa using hk
  have h := S.eq_one_of_mem_M_of_odd (e := S.z) S.z_mem_QG hN'C hN'n hodd' haN' (hN'C haN')
  rw [← e.apply_symm_apply k, h, map_one]

private theorem false_of_isConj_altX (S : Setting G) {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11)
    (e : G ≃* alternatingGroup (Fin n)) (hc : IsConj (altX h8) (e S.z)) : False := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hG : Nat.card G = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hM : Nat.card S.M * 2 = 8 * (n - 4).factorial := by
    have h1 := card_centralizer_altX h8
    rw [AS35W.card_centralizer_of_isConj hc,
      ← CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv e S.z] at h1
    exact h1
  clear hc e
  interval_cases n
  · have h2 := two_pow_dvd_card_M S (k := 6) (by rw [hG]; decide)
    norm_num [Nat.factorial] at hM h2
    omega
  · have h2 := two_pow_dvd_card_M S (k := 6) (by rw [hG]; decide)
    norm_num [Nat.factorial] at hM h2
    omega
  · have h2 := two_pow_dvd_card_M S (k := 7) (by rw [hG]; decide)
    norm_num [Nat.factorial] at hM h2
    omega
  · have h2 := two_pow_dvd_card_M S (k := 7) (by rw [hG]; decide)
    norm_num [Nat.factorial] at hM h2
    omega

private theorem false_of_isConj_altY_ten (S : Setting G) (hw : S.width = 2)
    (e : G ≃* alternatingGroup (Fin 10))
    (hc : IsConj (altY (n := 10) (by norm_num)) (e S.z)) : False := by
  apply false_of_card_M_eq_384 S hw
  have h1 := card_centralizer_altY (n := 10) (by norm_num)
  rw [AS35W.card_centralizer_of_isConj hc,
    ← CFSG.GH74.GLS.IVK.GHInv.card_centralizer_eq_of_mulEquiv e S.z] at h1
  change Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) = 384
  norm_num [Nat.factorial] at h1
  omega

private abbrev yPerm11 : Perm (Fin 11) := yPerm (by norm_num)

private abbrev altY11 : alternatingGroup (Fin 11) := altY (by norm_num)

private def cyc3 : Perm (Fin 11) := swap 8 9 * swap 9 10

private theorem eq_eight_or_nine_or_ten_of_yPerm11_apply_eq_self :
    ∀ k : Fin 11, yPerm11 k = k → k = 8 ∨ k = 9 ∨ k = 10 := by decide

private theorem cyc3_mul_yPerm11 : cyc3 * yPerm11 = yPerm11 * cyc3 := by decide

private theorem cyc3_pow_three : cyc3 ^ 3 = 1 := by decide

private theorem cyc3_ne_one : cyc3 ≠ 1 := by decide

private theorem swap_mul_swap_eq_cyc3_or : ∀ a b d : Fin 11, (a = 8 ∨ a = 9 ∨ a = 10) →
    (b = 8 ∨ b = 9 ∨ b = 10) → (d = 8 ∨ d = 9 ∨ d = 10) → a ≠ b → b ≠ d → a ≠ d →
    swap a b * swap b d = cyc3 ∨ swap a b * swap b d = cyc3 * cyc3 := by decide

private theorem sign_cyc3 : sign cyc3 = 1 := by
  rw [cyc3, map_mul, sign_swap (by decide), sign_swap (by decide)]
  rfl

private def alt3 : alternatingGroup (Fin 11) := ⟨cyc3, mem_alternatingGroup.2 sign_cyc3⟩

private theorem alt3_ne_one : alt3 ≠ 1 := fun h => cyc3_ne_one (Subtype.ext_iff.mp h)

private theorem orderOf_alt3 : orderOf alt3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime cyc3_pow_three cyc3_ne_one

private theorem alt3_mul_altY11 : alt3 * altY11 = altY11 * alt3 :=
  Subtype.ext cyc3_mul_yPerm11

private theorem conj_alt3_mem_zpowers {g : alternatingGroup (Fin 11)}
    (hg : g ∈ centralizer ({altY11} : Set (alternatingGroup (Fin 11)))) :
    g * alt3 * g⁻¹ ∈ zpowers alt3 := by
  have hgy : (g : Perm (Fin 11)) * yPerm11 = yPerm11 * (g : Perm (Fin 11)) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hglem : ∀ k : Fin 11, yPerm11 k = k →
      (g : Perm (Fin 11)) k = 8 ∨ (g : Perm (Fin 11)) k = 9 ∨ (g : Perm (Fin 11)) k = 10 := by
    intro k hk
    apply eq_eight_or_nine_or_ten_of_yPerm11_apply_eq_self
    have h := congrArg (fun σ : Perm (Fin 11) => σ k) hgy
    simp only [Equiv.Perm.mul_apply] at h
    rw [hk] at h
    exact h.symm
  have h8 := hglem 8 (by decide)
  have h9 := hglem 9 (by decide)
  have h10 := hglem 10 (by decide)
  have hne89 : (g : Perm (Fin 11)) 8 ≠ (g : Perm (Fin 11)) 9 := by
    intro h; exact (by decide : (8 : Fin 11) ≠ 9) ((g : Perm (Fin 11)).injective h)
  have hne910 : (g : Perm (Fin 11)) 9 ≠ (g : Perm (Fin 11)) 10 := by
    intro h; exact (by decide : (9 : Fin 11) ≠ 10) ((g : Perm (Fin 11)).injective h)
  have hne810 : (g : Perm (Fin 11)) 8 ≠ (g : Perm (Fin 11)) 10 := by
    intro h; exact (by decide : (8 : Fin 11) ≠ 10) ((g : Perm (Fin 11)).injective h)
  have hconj : (g : Perm (Fin 11)) * cyc3 * (g : Perm (Fin 11))⁻¹ =
      swap ((g : Perm (Fin 11)) 8) ((g : Perm (Fin 11)) 9) *
        swap ((g : Perm (Fin 11)) 9) ((g : Perm (Fin 11)) 10) := by
    have hdist : (g : Perm (Fin 11)) * cyc3 * (g : Perm (Fin 11))⁻¹ =
        ((g : Perm (Fin 11)) * swap 8 9 * (g : Perm (Fin 11))⁻¹) *
          ((g : Perm (Fin 11)) * swap 9 10 * (g : Perm (Fin 11))⁻¹) := by
      rw [cyc3]; group
    rw [hdist, ← swap_apply_apply (g : Perm (Fin 11)) 8 9,
      ← swap_apply_apply (g : Perm (Fin 11)) 9 10]
  have hswap := swap_mul_swap_eq_cyc3_or ((g : Perm (Fin 11)) 8) ((g : Perm (Fin 11)) 9)
    ((g : Perm (Fin 11)) 10) h8 h9 h10 hne89 hne910 hne810
  have hcoe : ((g * alt3 * g⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      (g : Perm (Fin 11)) * cyc3 * (g : Perm (Fin 11))⁻¹ := rfl
  have hsub : g * alt3 * g⁻¹ = alt3 ∨ g * alt3 * g⁻¹ = alt3 * alt3 := by
    rcases hswap with h | h
    · left; apply Subtype.ext; rw [hcoe, hconj]; simpa [alt3] using h
    · right; apply Subtype.ext; rw [hcoe, hconj]; simpa [alt3] using h
  rcases hsub with h | h
  · rw [h]; exact Subgroup.mem_zpowers alt3
  · rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_zpowers alt3) (Subgroup.mem_zpowers alt3)

private theorem false_of_eq_altY_eleven (S : Setting G) (e : G ≃* alternatingGroup (Fin 11))
    (he : e S.z = altY11) : False := by
  have hbot : zpowers alt3 = ⊥ := by
    refine eq_bot_of_odd_normal_centralizer_of_mulEquiv S e ?_ ?_ ?_
    · rw [he, Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr alt3_mul_altY11
    · rw [he]
      intro c hc k hk
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      rw [← conj_zpow]
      exact zpow_mem (conj_alt3_mem_zpowers hc) m
    · rw [Nat.card_zpowers, orderOf_alt3]
      decide
  exact alt3_ne_one (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers alt3))

private theorem exists_mulEquiv_apply_eq_of_isConj {H : Type} [Group H] (e : G ≃* H) {g : G}
    {a : H} (h : IsConj a (e g)) : ∃ e' : G ≃* H, e' g = a := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨e.trans (MulAut.conj c⁻¹), ?_⟩
  rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hc]
  group

theorem not_alternating_of_ten_le_of_le_eleven (S : Setting G) (hw : S.width = 2) {n : ℕ}
    (h10 : 10 ≤ n) (h11 : n ≤ 11) (e : G ≃* alternatingGroup (Fin n)) : False := by
  have h8 : 8 ≤ n := by omega
  have hz2 : orderOf (e S.z) = 2 := by rw [MulEquiv.orderOf_eq, S.orderOf_z]
  rcases AS35W.alt_inv_cases h8 h11 (e S.z) hz2 with hc | hc
  · exact false_of_isConj_altX S h8 h11 e hc
  · obtain rfl | rfl : n = 10 ∨ n = 11 := by omega
    · exact false_of_isConj_altY_ten S hw e hc
    · obtain ⟨e', he'⟩ := exists_mulEquiv_apply_eq_of_isConj e hc
      exact false_of_eq_altY_eleven S e' he'

end CFSG.GF2Type.Aschbacher1977
