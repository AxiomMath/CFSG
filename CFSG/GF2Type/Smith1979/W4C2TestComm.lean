module

public import CFSG.GF2Type.Smith1979.W4C2StructHm
public import CFSG.GF2Type.Smith1979.W4C2TestAlg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem valid_conj {F E : El} (hF : Valid F) (hE : Valid E) : Valid (conj F E) :=
  valid_mulE (valid_mulE hF hE) (valid_invE hF)

theorem dec_conj {F E : El} (hF : Valid F) (hE : Valid E) :
    dec (conj F E) = dec F * dec E * (dec F)⁻¹ := by
  unfold conj
  rw [dec_mul (valid_mulE hF hE) (valid_invE hF), dec_mul hF hE, dec_invE hF]

theorem dec_eq_of_eqE {E E' : El} (h : eqE E E' = true) : dec E = dec E' :=
  dec_congr (eqE_iff.mp h)

theorem valid_of_eqE {E E' : El} (h : eqE E E' = true) (hE : Valid E) : Valid E' :=
  (valid_congr (eqE_iff.mp h)).mp hE

theorem eqE_of_dec_eq {E E' : El} (h : Valid E) (h' : Valid E') (hd : dec E = dec E') :
    eqE E E' = true :=
  eqE_iff.mpr (dec_inj h h' hd)

theorem mem_stabL {H : List El} {b : Nat × Nat} {E : El} :
    E ∈ stabL H b ↔ E ∈ H ∧ eqV (appE E b) b = true := by
  simp [stabL]

theorem stabL_spec (hv : (Hlist ()).all validE = true) {b : Nat × Nat} {E : El}
    (hE : E ∈ stabL (Hlist ()) b) :
    Valid E ∧ dec E ∈ Hm ∧ dec E (vecE b) = vecE b := by
  obtain ⟨h1, h2⟩ := mem_stabL.mp hE
  have hval := valid_of_mem_Hlist hv h1
  refine ⟨hval, dec_mem_Hm hval, ?_⟩
  rw [dec_apply hval, ← vecE_appE]
  exact eqV_iff.mp h2

theorem exists_stabL (hv : (Hlist ()).all validE = true) {b : Nat × Nat}
    {f : Vm ≃ₗ[ZMod 2] Vm} (hf : f ∈ Hm) (hfb : f (vecE b) = vecE b) :
    ∃ E ∈ stabL (Hlist ()) b, Valid E ∧ f = dec E := by
  obtain ⟨E, hE, hval, rfl⟩ := exists_hlist_of_mem_Hm hv hf
  refine ⟨E, mem_stabL.mpr ⟨hE, ?_⟩, hval, rfl⟩
  rw [eqV_iff, vecE_appE, ← dec_apply hval]
  exact hfb

theorem comm_mem_Cl (hv : (Hlist ()).all validE = true) {b : Nat × Nat} {Cl : List El}
    (hcand : candOK (stabL (Hlist ()) b) Cl = true) {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)}
    (hLH : L ≤ Hm) (hLc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a) (hLs : ∀ a ∈ L, a * a = 1)
    (hLb : ∀ ℓ ∈ L, ℓ (vecE b) = vecE b)
    (hLn : ∀ m ∈ Hm, m (vecE b) = vecE b → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L) :
    ∀ ℓ ∈ L, ∃ C ∈ Cl, Valid C ∧ ℓ = dec C := by
  intro ℓ hℓ
  obtain ⟨E, hE, hEv, rfl⟩ := exists_stabL hv (hLH hℓ) (hLb ℓ hℓ)
  have hsq : eqE (mulE E E) idE = true := by
    refine eqE_of_dec_eq (valid_mulE hEv hEv) valid_idE ?_
    rw [dec_mul hEv hEv, dec_idE]
    exact hLs _ hℓ
  have hcomm : ∀ F ∈ stabL (Hlist ()) b, commuteE E (conj F E) = true := by
    intro F hF
    obtain ⟨hFv, hFm, hFb⟩ := stabL_spec hv hF
    have hmem := hLn _ hFm hFb _ hℓ
    have hcm := hLc _ hℓ _ hmem
    refine eqE_of_dec_eq (valid_mulE hEv (valid_conj hFv hEv))
      (valid_mulE (valid_conj hFv hEv) hEv) ?_
    rw [dec_mul hEv (valid_conj hFv hEv), dec_mul (valid_conj hFv hEv) hEv, dec_conj hFv hEv]
    exact hcm
  have key := List.all_eq_true.mp hcand E hE
  simp only [hsq, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at key
  rcases key with ⟨C, hC, hEC⟩ | ⟨F, hF, hFc⟩
  · exact ⟨C, hC, valid_of_eqE hEC hEv, dec_eq_of_eqE hEC⟩
  · rw [hcomm F hF] at hFc
    exact absurd hFc (by simp)

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
