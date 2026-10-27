module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymThreeBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphProd
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
  {S : ∀ j, Subgroup (G j)} {Λ : Subgroup (∀ j, G j)}

theorem pi_map_evalMonoidHom (j : Fin k) :
    (Subgroup.pi Set.univ S).map (Pi.evalMonoidHom G j) = S j := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_pi _).1 hx j (Set.mem_univ j)
  · intro b hb
    refine ⟨Pi.mulSingle j b, (Subgroup.mem_pi _).2 fun i _ => ?_, by simp⟩
    by_cases hij : i = j
    · subst hij
      simpa using hb
    · simp [Pi.mulSingle_eq_of_ne hij]

theorem le_pi_of_subnormal_symThree
    (hSΛ : Subgroup.pi Set.univ S ≤ Λ)
    (hΛS : Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ)
    {U : Subgroup (∀ j, G j)} (hUs : IsSubnormal U Λ)
    (hU : TwelveNotLe.Sym.IsSymThree U) :
    ∃ a s : ∀ j, G j, a ∈ U ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ s ∈ U ∧ s ^ 2 = 1 ∧ s ≠ 1 ∧
      s * a * s⁻¹ = a⁻¹ ∧ U = closure {a, s} ∧
      (∀ b ∈ U, b ^ 3 = 1 → b ≠ 1 → b = a ∨ b = a⁻¹) ∧
      IsSubnormal U (Subgroup.pi Set.univ S) := by
  classical
  obtain ⟨a, haU, ha1, ha3, hUa, ⟨s, hsU, hs2, hs1⟩, hUord⟩ := TwelveNotLe.Sym.symThree_data hU
  obtain ⟨hsa, hUeq⟩ := hUa s hsU hs2 hs1
  set N : Subgroup (∀ j, G j) := Subgroup.pi Set.univ S with hN
  have hNle : N ≤ Λ := hSΛ
  have hNnorm : (N.subgroupOf Λ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).2 hΛS
  haveI : (N.subgroupOf Λ).Normal := hNnorm
  have hsq_one : ∀ {H : Type} [Group H], Odd (Nat.card H) → ∀ {x : H}, x ^ 2 = 1 → x = 1 := by
    intro H _ hH x hx
    have h1 : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ dvd_rfl) (Odd.of_dvd_nat hH h1).not_two_dvd_nat
  have hmemN : ∀ x ∈ Λ, x ^ 2 = 1 → x ∈ N := by
    intro x hxΛ hx2
    have hoddQ : Odd (Nat.card (Λ ⧸ N.subgroupOf Λ)) := by
      apply Nat.not_even_iff_odd.1
      rw [even_iff_two_dvd]
      rwa [Subgroup.relIndex, Subgroup.index_eq_card] at hodd
    have hq2 : (QuotientGroup.mk' (N.subgroupOf Λ) ⟨x, hxΛ⟩) ^ 2 = 1 := by
      have hpow : (⟨x, hxΛ⟩ : Λ) ^ 2 = 1 := Subtype.ext hx2
      rw [← map_pow, hpow, map_one]
    have hq1 : (QuotientGroup.mk' (N.subgroupOf Λ) ⟨x, hxΛ⟩) = 1 := hsq_one hoddQ hq2
    have hq1' : (QuotientGroup.mk ⟨x, hxΛ⟩ : Λ ⧸ N.subgroupOf Λ) = 1 := by
      simpa [QuotientGroup.mk'_apply] using hq1
    exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 hq1')
  have hsΛ : s ∈ Λ := hUs.le hsU
  have haΛ : a ∈ Λ := hUs.le haU
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hsi : s⁻¹ = s := mul_eq_one_iff_inv_eq.mp hss
  have hsas : s * a * s = a⁻¹ := by simpa [hsi] using hsa
  have hsa2 : (s * a) ^ 2 = 1 := by
    rw [pow_two]
    calc (s * a) * (s * a) = (s * a * s) * a := by group
      _ = a⁻¹ * a := by rw [hsas]
      _ = 1 := inv_mul_cancel a
  have hsN : s ∈ N := hmemN s hsΛ hs2
  have hsaN : s * a ∈ N := hmemN (s * a) (Λ.mul_mem hsΛ haΛ) hsa2
  have haN : a ∈ N := by
    have h1 : s * (s * a) ∈ N := N.mul_mem hsN hsaN
    rwa [← mul_assoc, hss, one_mul] at h1
  have hUNle : U ≤ N := by
    rw [hUeq, Subgroup.closure_le]
    intro x hx
    rcases hx with hfl | hfl
    · rw [hfl]
      exact haN
    · rw [hfl]
      exact hsN
  have hUN : IsSubnormal U N := by
    have h := hUs.inf_of_le hNle
    rwa [inf_eq_left.2 hUNle] at h
  exact ⟨a, s, haU, ha1, ha3, hsU, hs2, hs1, hsa, hUeq, hUord, hUN⟩

theorem mulSingle_eq_or_inv_of_subnormal_symThree
    {U : Subgroup (∀ j, G j)} (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {s : ∀ j, G j} (hsU : s ∈ U) {j : Fin k} {b : G j}
    (hbS : b ∈ S j) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hinv : s j * b * (s j)⁻¹ = b⁻¹)
    {a : ∀ j, G j} (hUord : ∀ c ∈ U, c ^ 3 = 1 → c ≠ 1 → c = a ∨ c = a⁻¹) :
    Pi.mulSingle j b = a ∨ Pi.mulSingle j b = a⁻¹ := by
  have hbN : Pi.mulSingle j b ∈ Subgroup.pi Set.univ S := by
    rw [Subgroup.mem_pi]
    intro i _
    by_cases hij : i = j
    · subst hij
      simpa using hbS
    · simp [Pi.mulSingle_eq_of_ne hij]
  have hconj : s * Pi.mulSingle j b * s⁻¹ = (Pi.mulSingle j b)⁻¹ := by
    rw [TwelveNotLe.Prod.conj_mulSingle, hinv, Pi.mulSingle_inv]
  obtain ⟨n, hn⟩ := exists_iterate_commutator_mem hUN hsU hbN
  rw [iterate_commutator_of_conj_eq_inv hconj n] at hn
  have h2inv : b ^ 2 = b⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show 2 + 1 = 3 from rfl, hb3]
  have h4 : b ^ 4 = b := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hb3, one_mul]
  have hpar : ∀ m : ℕ, b ^ 2 ^ m = b ∨ b ^ 2 ^ m = b⁻¹ := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => left; simp
    | one => right; simpa using h2inv
    | more m ih0 ih1 =>
      have hstep : b ^ 2 ^ (m + 2) = b ^ 2 ^ m := by
        rw [show (2 : ℕ) ^ (m + 2) = 2 ^ m * 4 by rw [pow_add]; norm_num,
          Nat.mul_comm (2 ^ m) 4, pow_mul, h4]
      rw [hstep]
      exact ih0
  rw [← Pi.mulSingle_pow] at hn
  have hbmem : Pi.mulSingle j b ∈ U := by
    rcases hpar n with hb | hb
    · rw [hb] at hn
      exact hn
    · rw [hb, Pi.mulSingle_inv] at hn
      simpa using U.inv_mem hn
  have hpow : (Pi.mulSingle j b) ^ 3 = 1 := by
    rw [← Pi.mulSingle_pow, hb3]
    simp
  have hne : Pi.mulSingle j b ≠ 1 := by
    intro h
    exact hb1 (Pi.mulSingle_injective j (by simpa using h))
  exact hUord _ hbmem hpow hne

theorem projection_le_center_of_isQuasisimple
    {U : Subgroup (∀ j, G j)} (hU : TwelveNotLe.Sym.IsSymThree U)
    (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {j : Fin k} (hQ : CFSG.Open.IsQuasisimple ↥(S j)) :
    (U.map (Pi.evalMonoidHom G j)).subgroupOf (S j) ≤ Subgroup.center ↥(S j) := by
  obtain ⟨eU⟩ := hU
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  haveI : Group.IsSolvable ↥U :=
    Group.isSolvable_of_surjective (f := eU.symm.toMonoidHom) eU.symm.surjective
  set P : Subgroup (G j) := U.map (Pi.evalMonoidHom G j) with hP
  have hPle : P ≤ S j := by
    rw [← pi_map_evalMonoidHom (S := S) j]
    exact Subgroup.map_mono hUN.le
  have hPsub : IsSubnormal P (S j) := by
    have h := hUN.map (Pi.evalMonoidHom G j)
    rwa [pi_map_evalMonoidHom (S := S) j] at h
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_surjective
      (f := (Pi.evalMonoidHom G j).subgroupMap U)
      (MonoidHom.subgroupMap_surjective (Pi.evalMonoidHom G j) U)
  have hPsubj : IsSubnormal (P.subgroupOf (S j)) (⊤ : Subgroup ↥(S j)) := by
    rw [CFSG.Open.IsSubnormal.top_iff]
    exact (CFSG.Open.IsSubnormal.iff_subgroupOf hPle).1 hPsub
  have hcent : P.subgroupOf (S j) ≤ Subgroup.center ↥(S j) := by
    rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hQ
      (P.subgroupOf (S j)) hPsubj with h | h
    · exact h
    · exfalso
      haveI : Group.IsSolvable ↥(P.subgroupOf (S j)) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hPle).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hPle).injective
      haveI : Group.IsSolvable ↥(⊤ : Subgroup ↥(S j)) :=
        h ▸ (inferInstance : Group.IsSolvable ↥(P.subgroupOf (S j)))
      haveI : Group.IsSolvable ↥(S j) :=
        Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv (G := ↥(S j))).toMonoidHom)
          (Subgroup.topEquiv (G := ↥(S j))).surjective
      haveI : Group.IsPerfect ↥(S j) := ⟨hQ.1⟩
      haveI : Nontrivial ↥(S j) :=
        CFSG.ComponentClassification.Quasisimple.nontrivial hQ
      exact (Group.IsPerfect.not_isSolvable ↥(S j)) inferInstance
  exact hcent

theorem eq_one_coord_of_center
    {U : Subgroup (∀ j, G j)}
    {j : Fin k} (hZodd : Odd (Nat.card (Subgroup.center ↥(S j))))
    {a s : ∀ j, G j} (haU : a ∈ U) (hsU : s ∈ U)
    (hsa : s * a * s⁻¹ = a⁻¹) (hs2 : s ^ 2 = 1)
    (haS : a j ∈ S j) (hsS : s j ∈ S j)
    (hcent : (U.map (Pi.evalMonoidHom G j)).subgroupOf (S j) ≤ Subgroup.center ↥(S j)) :
    a j = 1 ∧ s j = 1 := by
  set P : Subgroup (G j) := U.map (Pi.evalMonoidHom G j) with hP
  have hcent' : P.subgroupOf (S j) ≤ Subgroup.center ↥(S j) := by
    simpa [hP] using hcent
  have hsjP : (⟨s j, hsS⟩ : ↥(S j)) ∈ P.subgroupOf (S j) := by
    rw [Subgroup.mem_subgroupOf, hP]
    exact Subgroup.mem_map_of_mem (Pi.evalMonoidHom G j) hsU
  have hajP : (⟨a j, haS⟩ : ↥(S j)) ∈ P.subgroupOf (S j) := by
    rw [Subgroup.mem_subgroupOf, hP]
    exact Subgroup.mem_map_of_mem (Pi.evalMonoidHom G j) haU
  have hsjc : (⟨s j, hsS⟩ : ↥(S j)) ∈ Subgroup.center ↥(S j) := hcent' hsjP
  have hajc : (⟨a j, haS⟩ : ↥(S j)) ∈ Subgroup.center ↥(S j) := hcent' hajP
  have hs2j : s j ^ 2 = 1 := by simpa using congrFun hs2 j
  have hcomm : s j * a j = a j * s j := by
    have h := (Subgroup.mem_center_iff.1 hsjc) ⟨a j, haS⟩
    exact (congrArg Subtype.val h).symm
  have hs_eq : (⟨s j, hsS⟩ : ↥(S j)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hs2j
  have ha_eq : (⟨a j, haS⟩ : ↥(S j)) ^ 2 = 1 := by
    have hini : s j * a j * (s j)⁻¹ = (a j)⁻¹ := by simpa using congrFun hsa j
    have h2 : s j * a j * (s j)⁻¹ = a j := by rw [hcomm]; group
    have haeq : a j = (a j)⁻¹ := h2.symm.trans hini
    have hsq : a j ^ 2 = 1 := by
      rw [pow_two]
      calc a j * a j = a j * (a j)⁻¹ := congrArg (fun x => a j * x) haeq
        _ = 1 := mul_inv_cancel (a j)
    apply Subtype.ext
    simpa using hsq
  have hsq_one : ∀ {H : Type} [Group H], Odd (Nat.card H) → ∀ {x : H}, x ^ 2 = 1 → x = 1 := by
    intro H _ hH x hx
    have h1 : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ dvd_rfl) (Odd.of_dvd_nat hH h1).not_two_dvd_nat
  have hs1j : s j = 1 := by
    have h := hsq_one hZodd (x := (⟨⟨s j, hsS⟩, hsjc⟩ : Subgroup.center ↥(S j))) ?_
    · simpa using congrArg (fun z : Subgroup.center ↥(S j) => ((z : ↥(S j)) : G j)) h
    · apply Subtype.ext
      exact hs_eq
  have ha1j : a j = 1 := by
    have h := hsq_one hZodd (x := (⟨⟨a j, haS⟩, hajc⟩ : Subgroup.center ↥(S j))) ?_
    · simpa using congrArg (fun z : Subgroup.center ↥(S j) => ((z : ↥(S j)) : G j)) h
    · apply Subtype.ext
      exact ha_eq
  exact ⟨ha1j, hs1j⟩

theorem eq_one_coord_of_isQuasisimple
    {U : Subgroup (∀ j, G j)} (hU : TwelveNotLe.Sym.IsSymThree U)
    (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {j : Fin k} (hQ : CFSG.Open.IsQuasisimple ↥(S j))
    (hZodd : Odd (Nat.card (Subgroup.center ↥(S j))))
    {a s : ∀ j, G j} (haU : a ∈ U) (hsU : s ∈ U)
    (hsa : s * a * s⁻¹ = a⁻¹) (hs2 : s ^ 2 = 1)
    (haS : a j ∈ S j) (hsS : s j ∈ S j) :
    a j = 1 ∧ s j = 1 :=
  eq_one_coord_of_center hZodd haU hsU hsa hs2 haS hsS
    (projection_le_center_of_isQuasisimple hU hUN hQ)

theorem eq_one_coord_of_isSUThreeTwo
    {U : Subgroup (∀ j, G j)} (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {a s : ∀ j, G j} (hsU : s ∈ U) (hsa : s * a * s⁻¹ = a⁻¹) (hs2 : s ^ 2 = 1)
    (ha3 : a ^ 3 = 1)
    (hUord : ∀ c ∈ U, c ^ 3 = 1 → c ≠ 1 → c = a ∨ c = a⁻¹)
    {j : Fin k} (hsS : s j ∈ S j)
    (hsuK : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (↥(S j) ≃* ↥(StatedSU 3 2 K))) :
    a j = 1 ∧ s j = 1 := by
  have hs1j : s j = 1 := by
    by_contra hs1j
    have hs2j : s j ^ 2 = 1 := by simpa using congrFun hs2 j
    have hs2' : (⟨s j, hsS⟩ : ↥(S j)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hs2j
    have hs1' : (⟨s j, hsS⟩ : ↥(S j)) ≠ 1 := by
      intro h
      exact hs1j (by simpa using congrArg Subtype.val h)
    obtain ⟨c, d, hc3, hd3, hcd, hcinv, hdinv⟩ :=
      exists_inv_noncomm_of_su hsuK hs2' hs1'
    have hc1 : (c : G j) ≠ 1 := by
      intro hc
      exact hcd (by rw [show c = 1 from Subtype.ext hc, one_mul, mul_one])
    have hd1 : (d : G j) ≠ 1 := by
      intro hd
      exact hcd (by rw [show d = 1 from Subtype.ext hd, mul_one, one_mul])
    have hc3' : (c : G j) ^ 3 = 1 := by simpa using congrArg Subtype.val hc3
    have hd3' : (d : G j) ^ 3 = 1 := by simpa using congrArg Subtype.val hd3
    have hcinv' : s j * (c : G j) * (s j)⁻¹ = (c : G j)⁻¹ := by
      simpa using congrArg Subtype.val hcinv
    have hdinv' : s j * (d : G j) * (s j)⁻¹ = (d : G j)⁻¹ := by
      simpa using congrArg Subtype.val hdinv
    have hc := mulSingle_eq_or_inv_of_subnormal_symThree hUN hsU c.2 hc3' hc1 hcinv' hUord
    have hd := mulSingle_eq_or_inv_of_subnormal_symThree hUN hsU d.2 hd3' hd1 hdinv' hUord
    have hcomm_mul : ∀ x y : ∀ i, G i, (x = a ∨ x = a⁻¹) → (y = a ∨ y = a⁻¹) →
        x * y = y * x := by
      intro x y hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rw [hx, hy]
      · rw [hx, hy, mul_inv_cancel, inv_mul_cancel]
      · rw [hx, hy, inv_mul_cancel, mul_inv_cancel]
      · rw [hx, hy]
    have hcomm_cd : Pi.mulSingle j (c : G j) * Pi.mulSingle j (d : G j) =
        Pi.mulSingle j (d : G j) * Pi.mulSingle j (c : G j) :=
      hcomm_mul _ _ hc hd
    have hcd' : (c : G j) * (d : G j) = (d : G j) * (c : G j) := by
      simpa using congrFun hcomm_cd j
    exact hcd (Subtype.ext hcd')
  refine ⟨?_, hs1j⟩
  have ha3j : a j ^ 3 = 1 := by simpa using congrFun ha3 j
  have hini : s j * a j * (s j)⁻¹ = (a j)⁻¹ := by simpa using congrFun hsa j
  rw [hs1j] at hini
  have haeq : a j = (a j)⁻¹ := by simpa using hini
  have ha2 : a j ^ 2 = 1 := by
    rw [pow_two]
    calc a j * a j = a j * (a j)⁻¹ := congrArg (fun x => a j * x) haeq
      _ = 1 := mul_inv_cancel (a j)
  exact TwelveNotLe.Sym.eq_one_of_pow_two_pow_three
    ⟨1, by simpa using ha2⟩ ⟨1, by simpa using ha3j⟩

theorem eq_one_coord_of_isSymThree
    {U : Subgroup (∀ j, G j)} (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {a s : ∀ j, G j} (hsU : s ∈ U) (hs2 : s ^ 2 = 1)
    (hUord : ∀ c ∈ U, c ^ 3 = 1 → c ≠ 1 → c = a ∨ c = a⁻¹)
    {j : Fin k} (hsS : s j ∈ S j) (haeq : a j = 1)
    (hsym : TwelveNotLe.Sym.IsSymThree (S j)) :
    s j = 1 := by
  by_contra hs1j
  obtain ⟨b, hbS, hb1, hb3, -, -, -⟩ := TwelveNotLe.Sym.symThree_data hsym
  obtain ⟨e⟩ := hsym
  have hinv : s j * b * (s j)⁻¹ = b⁻¹ := by
    have hs2j : s j ^ 2 = 1 := by simpa using congrFun hs2 j
    have hσ2 : (⟨s j, hsS⟩ : ↥(S j)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hs2j
    have hσ1 : (⟨s j, hsS⟩ : ↥(S j)) ≠ 1 := by
      intro h
      exact hs1j (by simpa using congrArg Subtype.val h)
    have hβ3 : (⟨b, hbS⟩ : ↥(S j)) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hb3
    have hβ1 : (⟨b, hbS⟩ : ↥(S j)) ≠ 1 := by
      intro h
      exact hb1 (by simpa using congrArg Subtype.val h)
    set σ : ↥(S j) := ⟨s j, hsS⟩ with hσdef
    set β : ↥(S j) := ⟨b, hbS⟩ with hβdef
    have hσ2' : (e σ) ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
    have hσ1' : e σ ≠ 1 := fun h => hσ1 (e.injective (h.trans (map_one e).symm))
    have hβ3' : (e β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hβ1' : e β ≠ 1 := fun h => hβ1 (e.injective (h.trans (map_one e).symm))
    have h := TwelveNotLe.Prod.perm3_invol_inv_of_order_three (e σ) hσ2' hσ1' (e β) hβ3' hβ1'
    have h' : σ * β * σ⁻¹ = β⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h
    simpa [σ, β] using congrArg Subtype.val h'
  have hb := mulSingle_eq_or_inv_of_subnormal_symThree hUN hsU hbS hb3 hb1 hinv hUord
  rcases hb with hb | hb
  · have h := congrFun hb j
    rw [Pi.mulSingle_eq_same, haeq] at h
    exact hb1 h
  · have h2 : b⁻¹ = a j := by
      have h := congrFun (congrArg Inv.inv hb) j
      simpa [Pi.mulSingle_eq_same] using h
    rw [haeq] at h2
    exact hb1 (by simpa using congrArg Inv.inv h2)

theorem eq_one_or_isSymThree_of_isWBlock
    {U : Subgroup (∀ j, G j)} (hU : TwelveNotLe.Sym.IsSymThree U)
    (hUN : IsSubnormal U (Subgroup.pi Set.univ S))
    {a s : ∀ j, G j} (haU : a ∈ U) (hsU : s ∈ U)
    (hsa : s * a * s⁻¹ = a⁻¹) (hs2 : s ^ 2 = 1) (ha3 : a ^ 3 = 1)
    (hUord : ∀ c ∈ U, c ^ 3 = 1 → c ≠ 1 → c = a ∨ c = a⁻¹)
    {j : Fin k} (hSj : S j = ⊥ ∨ IsWBlock ↥(S j))
    (haS : a j ∈ S j) (hsS : s j ∈ S j) :
    (a j = 1 ∧ s j = 1) ∨ TwelveNotLe.Sym.IsSymThree (S j) := by
  rcases hSj with hbot | hW
  · left
    rw [hbot] at haS hsS
    exact ⟨Subgroup.mem_bot.1 haS, Subgroup.mem_bot.1 hsS⟩
  · rw [IsWBlock] at hW
    rcases hW with ⟨hQ, hZodd⟩ | hSym
    · exact Or.inl
        (eq_one_coord_of_isQuasisimple hU hUN hQ hZodd haU hsU hsa hs2 haS hsS)
    · rw [IsSymThreeOrSUThreeTwo] at hSym
      rcases hSym with hsym | hsuK
      · exact Or.inr hsym
      · exact Or.inl (eq_one_coord_of_isSUThreeTwo hUN hsU hsa hs2 ha3 hUord hsS hsuK)

theorem eq_map_mulSingle_of_supported
    {U : Subgroup (∀ j, G j)} (hU : TwelveNotLe.Sym.IsSymThree U)
    {j : Fin k} (hsym : TwelveNotLe.Sym.IsSymThree (S j))
    {a s : ∀ j, G j} (hUeq : U = closure {a, s})
    (ha_supp : ∀ k, k ≠ j → a k = 1) (hs_supp : ∀ k, k ≠ j → s k = 1)
    (haS : a j ∈ S j) (hsS : s j ∈ S j) :
    U = (S j).map (MonoidHom.mulSingle G j) := by
  set A : Subgroup (∀ i, G i) := (S j).map (MonoidHom.mulSingle G j) with hA
  have hsupp : ∀ x : ∀ i, G i, x j ∈ S j → (∀ k, k ≠ j → x k = 1) → x ∈ A := by
    intro x hxS hx
    refine ⟨x j, hxS, ?_⟩
    ext k
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Pi.mulSingle_eq_of_ne hk, hx k hk]
  have hUA : U ≤ A := by
    rw [hUeq, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact hsupp a haS ha_supp
    · rw [hx]
      exact hsupp s hsS hs_supp
  haveI : Finite U := TwelveNotLe.Sym.finite_symThree hU
  have hUcard : Nat.card U = 6 := TwelveNotLe.Sym.card_symThree hU
  have hAcard : Nat.card A = 6 := by
    rw [hA, Subgroup.card_map_of_injective (Pi.mulSingle_injective j),
      TwelveNotLe.Sym.card_symThree hsym]
  refine Subgroup.eq_of_le_of_card_ge hUA ?_
  rw [hAcard, hUcard]

theorem exists_eq_map_mulSingle_of_subnormal_symThree
    (hSΛ : Subgroup.pi Set.univ S ≤ Λ)
    (hΛS : Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ)
    (hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    {U : Subgroup (∀ j, G j)} (hUs : IsSubnormal U Λ)
    (hU : TwelveNotLe.Sym.IsSymThree U) :
    ∃ j, U = (S j).map (MonoidHom.mulSingle G j) := by
  classical
  obtain ⟨a, s, haU, ha1, ha3, hsU, hs2, -, hsa, hUeq, hUord, hUN⟩ :=
    le_pi_of_subnormal_symThree hSΛ hΛS hodd hUs hU
  have haS : ∀ j, a j ∈ S j := fun j => (Subgroup.mem_pi _).1 (hUN.le haU) j (Set.mem_univ j)
  have hsS : ∀ j, s j ∈ S j := fun j => (Subgroup.mem_pi _).1 (hUN.le hsU) j (Set.mem_univ j)
  obtain ⟨j0, hj0⟩ : ∃ j, a j ≠ 1 := by
    by_contra h
    push Not at h
    exact ha1 (funext h)
  have hj0sym : TwelveNotLe.Sym.IsSymThree (S j0) := by
    rcases eq_one_or_isSymThree_of_isWBlock hU hUN haU hsU hsa hs2 ha3 hUord (hS j0)
      (haS j0) (hsS j0) with ⟨ha0, -⟩ | hsym
    · exact absurd ha0 hj0
    · exact hsym
  have hmain := mulSingle_eq_or_inv_of_subnormal_symThree hUN hsU (haS j0)
    (by simpa using congrFun ha3 j0) hj0 (by simpa using congrFun hsa j0) hUord
  have ha_supp : ∀ k, k ≠ j0 → a k = 1 := by
    intro k hk
    obtain ⟨x, hx⟩ : ∃ x : G j0, a = Pi.mulSingle j0 x := by
      rcases hmain with h | h
      · exact ⟨a j0, h.symm⟩
      · refine ⟨(a j0)⁻¹, ?_⟩
        calc a = (a⁻¹)⁻¹ := (inv_inv a).symm
          _ = (Pi.mulSingle j0 (a j0))⁻¹ := by rw [h]
          _ = Pi.mulSingle j0 ((a j0)⁻¹) := (Pi.mulSingle_inv j0 (a j0)).symm
    simpa [Pi.mulSingle_eq_of_ne hk] using congrFun hx k
  have hs_supp : ∀ k, k ≠ j0 → s k = 1 := by
    intro k hk
    have hak : a k = 1 := ha_supp k hk
    rcases eq_one_or_isSymThree_of_isWBlock hU hUN haU hsU hsa hs2 ha3 hUord (hS k)
      (haS k) (hsS k) with ⟨-, hs1⟩ | hsym
    · exact hs1
    · exact eq_one_coord_of_isSymThree hUN hsU hs2 hUord (hsS k) hak hsym
  exact ⟨j0, eq_map_mulSingle_of_supported hU hj0sym hUeq ha_supp hs_supp (haS j0) (hsS j0)⟩

theorem le_normalizer_of_subnormal_symThree
    (hSΛ : Subgroup.pi Set.univ S ≤ Λ)
    (hΛS : Λ ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hodd : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ)
    (hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j))
    {U : Subgroup (∀ j, G j)} (hUs : IsSubnormal U Λ)
    (hU : TwelveNotLe.Sym.IsSymThree U) :
    Λ ≤ normalizer (U : Set (∀ j, G j)) := by
  obtain ⟨j, hj⟩ := exists_eq_map_mulSingle_of_subnormal_symThree hSΛ hΛS hodd hS hUs hU
  rw [hj]
  have hconj : ∀ (t : ∀ j, G j), t ∈ Λ →
      ∀ x ∈ (S j).map (MonoidHom.mulSingle G j),
        t * x * t⁻¹ ∈ (S j).map (MonoidHom.mulSingle G j) := by
    intro t ht x hx
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨t j * b * (t j)⁻¹, ?_, ?_⟩
    · have hbN : Pi.mulSingle j b ∈ Subgroup.pi Set.univ S := by
        rw [Subgroup.mem_pi]
        intro i _
        by_cases hij : i = j
        · subst hij
          simpa using hb
        · simp [Pi.mulSingle_eq_of_ne hij]
      have htN : t * Pi.mulSingle j b * t⁻¹ ∈ Subgroup.pi Set.univ S :=
        ((Subgroup.mem_normalizer_iff.1 (hΛS ht)) (Pi.mulSingle j b)).1 hbN
      simpa using (Subgroup.mem_pi _).1 htN j (Set.mem_univ j)
    · simpa using (TwelveNotLe.Prod.conj_mulSingle t j b).symm
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hconj t ht x hx
  · intro hx
    have h := hconj t⁻¹ (Λ.inv_mem ht) (t * x * t⁻¹) hx
    have hx' : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [hx'] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
