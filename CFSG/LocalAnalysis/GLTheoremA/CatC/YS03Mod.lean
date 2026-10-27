module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveHSMcL
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestRu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestON
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestHe
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Solomon.Coordinator

section Kit

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem ys03_oPrime_inf_conj {P R : Subgroup G} (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {k : G}
    (hk : k ∈ R) {x : G}
    (h : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P) = ⊥) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({k * x * k⁻¹} : Set G) ⊓ P) = ⊥ := by
  have hk' : ∀ q ∈ P, k⁻¹ * q * k ∈ P := fun q hq => by
    simpa using hR k⁻¹ (R.inv_mem hk) q hq
  rw [← map_conj_centralizer_inf (hR k hk) hk' x,
    ← map_glaPPrimeCoreOf_of_injective p (MulAut.conj k).toMonoidHom (MulAut.conj k).injective, h,
    Subgroup.map_bot]

theorem ys03_oPrime_of_lines (hp : p.Prime) {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    (hline : ∀ j, GLAPPrimeCoreOf p (Subgroup.centralizer ({line j} : Set G) ⊓ P) = ⊥) :
    ∀ y ∈ P, orderOf y = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G) ⊓ P) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro y hyP hyo
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP hQ hyP hyo
  set t := g⁻¹ * y * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, htdef, hyo] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have ht : GLAPPrimeCoreOf p (Subgroup.centralizer ({t} : Set G) ⊓ P) = ⊥ := by
    rw [centralizer_singleton_eq_of_zpowers hj]
    exact hline j
  have hy : y = g * t * g⁻¹ := by rw [htdef]; group
  rw [hy]
  exact ys03_oPrime_inf_conj (R := P)
    (fun r hr q hq => P.mul_mem (P.mul_mem hr hq) (P.inv_mem hr)) hgP ht

theorem ys03_oPrimeCoreTrivialAt_of_sub (P : Subgroup G)
    (h : ∀ x ∈ P, orderOf x = p →
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P) = ⊥) :
    OPrimeCoreTrivialAt p ↥P := by
  intro x hx
  have h1 := h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype P x,
    ← map_glaPPrimeCoreOf_of_injective p P.subtype P.subtype_injective] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 h1

end Kit

section HSMcL

open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Sporadic.Schreier


theorem ys03_oPrime_five_hs100P : OPrimeCoreTrivialAt 5 ↥hs100P := by
  obtain ⟨⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩, -⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := hs_autModel
  refine ys03_oPrimeCoreTrivialAt_of_sub hs100P
    (ys03_oPrime_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) hs100FiveLine
      (lines_of_eq hlines) fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : hs100FiveRecordOf j = 0 ∨ hs100FiveRecordOf j = 2 ∨ hs100FiveRecordOf j = 23 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rw [← hjconj]
  exact ys03_oPrime_inf_conj hM.conj_mem hjR
    (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
      (gLAPPrimeCoreOf_hs100FiveRecord_eq_bot _ hr))

theorem ys03_oPrime_five_mcl275P : OPrimeCoreTrivialAt 5 ↥mcl275P := by
  obtain ⟨-, ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩⟩ :=
    R3E_HS_McL_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := mcl_autModel
  refine ys03_oPrimeCoreTrivialAt_of_sub mcl275P
    (ys03_oPrime_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) mcl275FiveLine
      (lines_of_eq hlines) fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : mcl275FiveRecordOf j = 0 ∨ mcl275FiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rw [← hjconj]
  exact ys03_oPrime_inf_conj hM.conj_mem hjR
    (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
      (gLAPPrimeCoreOf_mcl275FiveRecord_eq_bot _ hr))

section HS


theorem ys03_sporadicOPrimeHolds_HS_five : SporadicOPrimeHolds .HS 5 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans hs100Equiv) ys03_oPrime_five_hs100P

end HS

section McL


theorem ys03_sporadicOPrimeHolds_McL_five : SporadicOPrimeHolds .McL 5 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans mclPermEquiv)
    ys03_oPrime_five_mcl275P

end McL

end HSMcL

section Ru

open CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier


theorem ys03_oPrime_five_ruP : OPrimeCoreTrivialAt 5 ↥ruP := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_Ru_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine ys03_oPrimeCoreTrivialAt_of_sub ruP
    (ys03_oPrime_of_lines Nat.prime_five hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) ruFiveLine
      (lines_of_eq hlines) fun j => ?_)
  obtain ⟨hjP, hjconj⟩ := htrans j
  have hr : ruFiveRecordOf j = 0 ∨ ruFiveRecordOf j = 1 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rw [← hjconj]
  exact ys03_oPrime_inf_conj (R := ruP)
    (fun r hr q hq => ruP.mul_mem (ruP.mul_mem hr hq) (ruP.inv_mem hr)) hjP
    (gLAPPrimeCoreOf_ruFiveRecord_eq_bot _ hr)

theorem ys03_sporadicOPrimeHolds_Ru_five : SporadicOPrimeHolds .Ru 5 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans ruEquivP) ys03_oPrime_five_ruP

end Ru

section ON

open CFSG.RankThree.Native CFSG.ONSchreier


theorem ys03_oPrime_seven_Pv : OPrimeCoreTrivialAt 7 ↥Pv := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, -, -, -, htrans, hcover⟩ :=
    R3E_ON_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  have hPn : ∀ r ∈ Pv, ∀ q ∈ Pv, r * q * r⁻¹ ∈ Pv := fun r hr q hq =>
    Pv.mul_mem (Pv.mul_mem hr hq) (Pv.inv_mem hr)
  refine ys03_oPrimeCoreTrivialAt_of_sub Pv
    (ys03_oPrime_of_lines hp7 hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) onSevenLine
      (lines_of_eq hlines) fun j => ?_)
  obtain ⟨r, t, ht, htj⟩ := hcover j
  obtain ⟨htP, hpow1, hpow6, hj, hconj⟩ := htrans r t ht
  have hjj : (⟨t.line, hj⟩ : Fin 57) = j := Fin.ext htj
  rw [hjj] at hconj
  set h := onSevenTransporterPerm t
  set x := onSevenLine (onSevenRep r)
  have hxo : orderOf x = 7 := orderOf_onSevenLine (onSevenRep r)
  have hyo : orderOf (h * x * h⁻¹) = 7 := by
    have := (MulAut.conj h : Equiv.Perm (Fin N) ≃* Equiv.Perm (Fin N)).orderOf_eq x
    simpa [MulAut.conj_apply, hxo] using this
  have hz : Subgroup.zpowers (onSevenLine j) = Subgroup.zpowers (h * x * h⁻¹) := by
    rw [← hconj]
    exact zpowers_pow_eq_of_lt_prime hp7 hyo (by omega) (by omega)
  rw [centralizer_singleton_eq_of_zpowers hz]
  exact ys03_oPrime_inf_conj hPn htP (gLAPPrimeCoreOf_onSevenRecord_eq_bot r)

theorem ys03_sporadicOPrimeHolds_ONan_seven : SporadicOPrimeHolds .ONan 7 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans onEquivPv) ys03_oPrime_seven_Pv

end ON

section He

open CFSG.RankThree.PartOne CFSG.Sporadic.HeldB


theorem ys03_oPrime_seven_heP : OPrimeCoreTrivialAt 7 ↥heP := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_He_full_seven_centralizer_structures
  have hp7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  have hM := heAutModel
  refine ys03_oPrimeCoreTrivialAt_of_sub heP
    (ys03_oPrime_of_lines hp7 hQP (card_eq_of_sylow_subgroupOf hQP hQsyl) heSevenLine
      (lines_of_eq hlines) fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hr : heSevenRecordOf j = 0 ∨ heSevenRecordOf j = 1 ∨ heSevenRecordOf j = 2 := by
    have h := hrecmem j
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rw [← hjconj]
  exact ys03_oPrime_inf_conj hM.conj_mem hjR
    (gLAPPrimeCoreOf_inf_eq_bot_of_ambient hp7 hM.le hM.conj_mem
      (gLAPPrimeCoreOf_heSevenRecord_eq_bot _ hr))

theorem ys03_sporadicOPrimeHolds_He_seven : SporadicOPrimeHolds .He 7 :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans heEquivP) ys03_oPrime_seven_heP

end He

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
