module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicConjW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW3
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24Tests

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M24

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.M22
open CFSG.ABGLocalTools CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.Code

@[expose] def m24CheckC (xg xs : Array (Array ℕ)) (xw : List (List ℕ)) (d : ConjData)
    (e0 : Array (Array ℕ)) (wit : Wit) (cl : ClosW) : Bool :=
  (allLt xg.size fun k => validK 24 xg[k]! && autA xg[k]!) && xsOK 24 xg xs xw &&
    conjCensusOKW 24 m22PS (inXL 24 xs) allA (inXL 24 xs) true false false d e0 &&
    d.xs.all (inXL 24 xs) && d.xs.length == 10 && enumOKK 24 e0 m22PS (maskCert 24 e0) &&
    witOKW3 24 m22PS (inXL 24 xs) allA false false true e0 (maskCert 24 e0) #[] default cl wit

theorem census_of_m24CheckC {xg xs : Array (Array ℕ)}
    {xw : List (List ℕ)} {d : ConjData} {e0 : Array (Array ℕ)} {wit : Wit} {cl : ClosW}
    (h : m24CheckC xg xs xw d e0 wit cl = true) :
    YCensus17U (⊤ : Subgroup ↥AutPerm) (fun _ => False) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [m24CheckC, validK_eq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hxg, hxs⟩, hc⟩, hgen⟩, hlen⟩, he0⟩, hw0⟩ := h
  have hGv : (allLt xg.size fun k => validA 24 xg[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact this.1
  have hGX : closure (permsA 24 xg) ≤ AutPerm := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have := allLt_spec hxg hk
    simp only [Bool.and_eq_true] at this
    exact mem_AutPerm_of_autA this.2
  have hin : ∀ a, validA 24 a = true → inXL 24 xs a = true → permOfArr 24 a ∈ AutPerm :=
    fun a hv ha => hGX (mem_closure_of_inXL hGv hxs hv ha)
  have hout : ∀ a, validA 24 a = true → permOfArr 24 a ∈ AutPerm → allA a = true :=
    fun _ _ _ => rfl
  have hc' := hc
  simp only [conjCensusOKW, Bool.and_eq_true] at hc'
  obtain ⟨hxv, -, -⟩ := pc_of_pcOK hc'.1.1.1.1.1
  set S' := pcSub 24 d.xs
  have hS'R : S' ≤ AutPerm := by
    refine (closure_le _).2 fun _ hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hin _ (hxv a ha) (List.all_eq_true.1 hgen a ha)
  have hSX : ∀ s ∈ S', AutPerm.map (MulAut.conj s).toMonoidHom = AutPerm := by
    intro s hs
    have hsR := hS'R hs
    refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hsR hx) (inv_mem hsR)
    · exact mul_mem (mul_mem (inv_mem hsR) hx) hsR
    · simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨hS'card, hw⟩ := census_of_conjCensusOKW m22PS_lt hin hout hin hS'R hSX hc
  set E₀ := closure (permsA 24 e0)
  have hw0' := witOKW3_sound (X := AutPerm) m22PS_lt hin hout (enumOK_of_enumOKK he0) hw0
  have hexc : ∀ v ∈ AutPerm, 4 ≤ Nat.card (E₀.map (MulAut.conj v).toMonoidHom) →
      WitW AutPerm false false true (E₀.map (MulAut.conj v).toMonoidHom) := by
    intro v hv h4
    have h4' : 4 ≤ Nat.card E₀ := by
      rwa [card_map_of_injective (MulAut.conj v).injective] at h4
    have hW : WitW AutPerm false false true E₀ := by
      rcases hw0' with hm | ⟨-, hw⟩
      · exact witW_of_monoW false true hm le_rfl
      · exact hw h4'
    have hvX : AutPerm.map (MulAut.conj v⁻¹).toMonoidHom = AutPerm := by
      refine le_antisymm ?_ fun x hx => ⟨v * x * v⁻¹, ?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mul_mem (mul_mem (inv_mem hv) hx) (inv_inv v ▸ hv)
      · exact mul_mem (mul_mem hv hx) (inv_mem hv)
      · simp [MulAut.conj_apply, mul_assoc]
    have hback : (E₀.map (MulAut.conj v).toMonoidHom).map (MulAut.conj v⁻¹).toMonoidHom = E₀ := by
      rw [map_conj_map_conj, inv_mul_cancel]
      ext x
      simp [MulAut.conj_apply]
    exact witW_of_map_conj hvX (by rw [hback]; exact hW)
  have hS'le : S' ≤ iota.range := by
    change S' ≤ AutPerm.subtype.range
    rw [range_subtype]
    exact hS'R
  set S := S'.comap iota
  have hSmap : S.map iota = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 1024 := by
    rw [← card_map_of_injective iota_injective, hSmap, hS'card, hlen]
    norm_num
  have hSyl : IsSylowOf 2 S ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card (n := 10) (by rw [hScard]; norm_num), ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, card_AutPerm] at h1
    omega
  refine yCensus17U_of_le_sylow inferInstance hSyl (fun _ _ h => h) fun E hES hE hE4 _ => ?_
  have hES' : E.map iota ≤ S' := hSmap ▸ map_mono hES
  have hE4' : 4 ≤ Nat.card (E.map iota) := by rwa [card_map_of_injective iota_injective]
  have key : WitW ((⊤ : Subgroup ↥AutPerm).map iota) true false false (E.map iota) ∨
      WitW ((⊤ : Subgroup ↥AutPerm).map iota) false false true (E.map iota) := by
    rw [map_top_iota]
    rcases hw _ hES' (isElemAbelian_map hE iota) hE4' with hw | ⟨v, hv, heq⟩
    · exact Or.inl hw
    · rw [heq] at hE4' ⊢
      exact Or.inr (hexc v hv hE4')
  rcases key with (hw | hw | ⟨h, -⟩ | ⟨h, -⟩) | (hw | ⟨h, -⟩ | ⟨h, -⟩ | hw)
  · exact Or.inl ((yWitness_map_iff iota iota_injective _ _).mp hw)
  · exact Or.inr (Or.inl ((pWitness_map_iff iota iota_injective _ _).mp hw.2))
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inl ((yWitness_map_iff iota iota_injective _ _).mp hw)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inr (Or.inr ((uWitness_map_iff iota iota_injective _ _).mp hw.2))

theorem sporadicCaseOdd_M24_ofC
    (hc : center ↥Blueprint.NativeSporadic.M24 = ⊥)
    (hi : OuterAutomorphisms.inner ↥Blueprint.NativeSporadic.M24 = ⊤)
    (hM : OddMultiplier (Blueprint.NativeSporadic.Carrier .M24)) {xg xs : Array (Array ℕ)}
    {xw : List (List ℕ)} {d : ConjData} {e0 : Array (Array ℕ)} {wit : Wit} {cl : ClosW}
    (hs : m24CheckC xg xs xw d e0 wit cl = true) (h32 : AS76b.Lemma32)
    (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .M24 :=
  sporadicCaseOdd_of_yCensus17U h32 h33 hM (m24AutModel_of hc hi) m24_commutator_le
    m24_yCensusII (census_of_m24CheckC hs)

end CFSG.ComponentClassification.RankTwoSporadic.M24
