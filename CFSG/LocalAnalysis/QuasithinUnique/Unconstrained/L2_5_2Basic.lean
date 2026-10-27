module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools

public section

namespace CFSG.QuasithinUnique.Unc25G2

open CFSG.Open CFSG.Quasithin

section CharTwoProducts

variable {G : Type*} [Group G]

theorem charTwo_bot : CharTwo (⊥ : Subgroup G) := by
  intro x hx
  have : x = 1 := Subgroup.mem_bot.mp hx.1
  rw [this]
  exact Subgroup.one_mem _

theorem pow_mul_mem_of_mem_normalizer {Y : Subgroup G} {s y : G}
    (hs : s ∈ Subgroup.normalizer (Y : Set G)) (hy : y ∈ Y) (n : ℕ) :
    ∃ y' ∈ Y, (s * y) ^ n = s ^ n * y' := by
  induction n with
  | zero => exact ⟨1, Y.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨y', hy', h⟩ := ih
    have hconj : s⁻¹ * y' * s ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) y').mp hy'
      simpa using this
    refine ⟨s⁻¹ * y' * s * y, Y.mul_mem hconj hy, ?_⟩
    rw [pow_succ, h]
    group

theorem charTwo_sup_of_isPGroup_le_normalizer {Y S : Subgroup G} (hY : CharTwo Y)
    (hS : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G)) : CharTwo (Y ⊔ S) := by
  set J := Y ⊔ S with hJ
  have hYJ : Y ≤ J := le_sup_left
  have hJY : J ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  set P := pCoreOf 2 Y with hP
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 Y
  have hPY : P ≤ Y := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 Y
  have hJP : J ≤ Subgroup.normalizer (P : Set G) :=
    hJY.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 Y)
  have hPJ : P ≤ pCoreOf 2 J :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 P J (hPY.trans hYJ)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hPY.trans hYJ)).mpr hJP) hP2
  have hC2 : IsPGroup 2 ↥(J ⊓ Subgroup.centralizer (P : Set G)) := by
    intro c
    have hcJ : (c : G) ∈ ((S ⊔ Y : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact c.2.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S Y hSY] at hcJ
    obtain ⟨s, hs, y, hy, hsy⟩ := hcJ
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨y', hy', hpow⟩ := pow_mul_mem_of_mem_normalizer (hSY hs) hy (2 ^ k)
    have hcy : (c : G) ^ 2 ^ k = y' := by
      rw [← hsy, hpow, hsk, one_mul]
    have hy'c : y' ∈ Subgroup.centralizer (P : Set G) := by
      rw [← hcy]
      exact Subgroup.pow_mem _ c.2.2 _
    have hy'P : y' ∈ P := hY ⟨hy', hy'c⟩
    obtain ⟨m, hm⟩ := hP2 ⟨y', hy'P⟩
    have hm' : y' ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine ⟨k + m, Subtype.ext ?_⟩
    show (c : G) ^ 2 ^ (k + m) = 1
    rw [pow_add, pow_mul, hcy, hm']
  have hJC : J ≤ Subgroup.normalizer ((J ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf J J _
      Subgroup.le_normalizer
      (hJP.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer P))
  have hCR : J ⊓ Subgroup.centralizer (P : Set G) ≤ pCoreOf 2 J :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ J inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hJC) hC2
  intro x hx
  exact hCR ⟨hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPJ) hx.2⟩

theorem charTwo_sup_of_commute {A B : Subgroup G} (hA : CharTwo A) (hB : CharTwo B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : CharTwo (A ⊔ B) := by
  set J := A ⊔ B with hJ
  set PA := pCoreOf 2 A with hPA
  set PB := pCoreOf 2 B with hPB
  have hPA2 : IsPGroup 2 PA := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 A
  have hPB2 : IsPGroup 2 PB := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 B
  have hPAA : PA ≤ A := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 A
  have hPBB : PB ≤ B := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 B
  have hAJ : A ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  have hAPB : A ≤ Subgroup.normalizer (PB : Set G) := by
    refine le_trans (fun a ha => ?_) (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => (hAB a ha w (hPBB hw)).symm
  have hBPA : B ≤ Subgroup.normalizer (PA : Set G) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => hAB w (hPAA hw) b hb
  have hAPA : A ≤ Subgroup.normalizer (PA : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 A
  have hBPB : B ≤ Subgroup.normalizer (PB : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 B
  set D := PA ⊔ PB with hD
  have hD2 : IsPGroup 2 ↥D := hPA2.to_sup_of_normal_right' hPB2 (hPAA.trans hAPB)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf hAPA hAPB).trans (Subgroup.inf_normalizer_le_normalizer_sup PA PB)
  have hBD : B ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf hBPA hBPB).trans (Subgroup.inf_normalizer_le_normalizer_sup PA PB)
  have hJD : J ≤ Subgroup.normalizer (D : Set G) := sup_le hAD hBD
  have hDJ : D ≤ J := sup_le (hPAA.trans hAJ) (hPBB.trans hBJ)
  have hDR : D ≤ pCoreOf 2 J :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 D J hDJ
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDJ).mpr hJD) hD2
  intro x hx
  apply hDR
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hx.1
  have hxc := Subgroup.mem_centralizer_iff.mp hx.2
  have haPA : a ∈ PA := by
    refine hA ⟨ha, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 := hxc w (hDR (Subgroup.mem_sup_left hw))
    have hbw : b * w = w * b := (hAB w (hPAA hw) b hb).symm
    have : w * a * b = a * w * b := by
      calc w * a * b = w * (a * b) := by rw [mul_assoc]
        _ = a * b * w := h1
        _ = a * (b * w) := by rw [mul_assoc]
        _ = a * (w * b) := by rw [hbw]
        _ = a * w * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hbPB : b ∈ PB := by
    refine hB ⟨hb, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 := hxc w (hDR (Subgroup.mem_sup_right hw))
    have haw : a * w = w * a := hAB a ha w (hPBB hw)
    have : a * (w * b) = a * (b * w) := by
      calc a * (w * b) = a * w * b := by rw [mul_assoc]
        _ = w * a * b := by rw [haw]
        _ = w * (a * b) := by rw [mul_assoc]
        _ = a * b * w := h1
        _ = a * (b * w) := by rw [mul_assoc]
    exact mul_left_cancel this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haPA) (Subgroup.mem_sup_right hbPB)

theorem charTwo_finset_sup_of_commute (F : Finset (Subgroup G)) (hF : ∀ A ∈ F, CharTwo A)
    (hcomm : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    CharTwo (F.sup id) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using charTwo_bot
  | insert A F hAF ih =>
    rw [Finset.sup_insert]
    have h1 : CharTwo (F.sup id) :=
      ih (fun B hB => hF B (Finset.mem_insert_of_mem hB))
        (fun B hB C hC => hcomm B (Finset.mem_insert_of_mem hB) C (Finset.mem_insert_of_mem hC))
    have hA : CharTwo A := hF A (Finset.mem_insert_self A F)
    have hle : F.sup id ≤ Subgroup.centralizer (A : Set G) := by
      refine Finset.sup_le fun B hB => fun b hb => ?_
      have hne : A ≠ B := fun h => hAF (h ▸ hB)
      exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
        hcomm A (Finset.mem_insert_self A F) B (Finset.mem_insert_of_mem hB) hne a ha b hb
    exact charTwo_sup_of_commute hA h1 fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hle hb) a ha

end CharTwoProducts

section Conjugation

variable {G : Type*} [Group G]

theorem map_conj_conj (g h : G) (X : Subgroup G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      X.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext w
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map]

theorem map_conj_eq_of_mem_normalizer' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hmem : g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have hyy' : y' = y := by simpa [MulAut.conj_apply] using hyy
    rw [← hyy']
    exact hy'

theorem map_conj_eq_of_map_conj_eq {S L K : Subgroup G}
    (hK : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    {s t : G} (hs : s ∈ S) (ht : t ∈ S)
    (h : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) :
    K.map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj t).toMonoidHom := by
  have hLg : L.map (MulAut.conj (t⁻¹ * s)).toMonoidHom = L := by
    rw [← map_conj_conj s t⁻¹ L, h, map_conj_conj t t⁻¹ L, inv_mul_cancel, map_conj_one]
  have hg : t⁻¹ * s ∈ S ⊓ Subgroup.normalizer (L : Set G) :=
    ⟨S.mul_mem (S.inv_mem ht) hs, mem_normalizer_of_map_conj_eq hLg⟩
  have hKg : K.map (MulAut.conj (t⁻¹ * s)).toMonoidHom = K :=
    map_conj_eq_of_mem_normalizer' (hK hg)
  calc K.map (MulAut.conj s).toMonoidHom
      = K.map (MulAut.conj (t * (t⁻¹ * s))).toMonoidHom := by rw [mul_inv_cancel_left]
    _ = (K.map (MulAut.conj (t⁻¹ * s)).toMonoidHom).map (MulAut.conj t).toMonoidHom :=
        (map_conj_conj _ _ K).symm
    _ = K.map (MulAut.conj t).toMonoidHom := by rw [hKg]

theorem inf_normalizer_le_normalizer_borel (S L : Subgroup G) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :
        Subgroup G) : Set G) := by
  have h1 : S ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ S L
      (inf_le_left.trans Subgroup.le_normalizer) inf_le_right
  exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ L _
    inf_le_right (h1.trans Subgroup.le_normalizer)

theorem inf_normalizer_le_normalizer_inf_of_le {S L M : Subgroup G} (hSM : S ≤ M) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ M L
    ((inf_le_left.trans hSM).trans Subgroup.le_normalizer) inf_le_right

end Conjugation

section Components

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isComponentIn_map_conj {L H : Subgroup G} (hL : IsComponentIn L H) {s : G} (hs : s ∈ H) :
    IsComponentIn (L.map (MulAut.conj s).toMonoidHom) H := by
  have h := isComponentIn_conjugate hL (H.inv_mem hs)
  simpa only [CFSG.conjugate, inv_inv] using h

theorem charTwo_conjJoin_of_component {H S L K : Subgroup G} (hSH : S ≤ H)
    (hL : IsComponentIn L H) (hKL : K ≤ L)
    (hK : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hKc : CharTwo K) : CharTwo (conjJoin S K) := by
  classical
  have : Fintype ↥S := Fintype.ofFinite _
  let f : ↥S → Subgroup G := fun s => K.map (MulAut.conj (s : G)).toMonoidHom
  have hconjJ : conjJoin S K = (Finset.univ.image f).sup id := by
    rw [Finset.sup_image, Finset.sup_univ_eq_iSup]
    rfl
  rw [hconjJ]
  refine charTwo_finset_sup_of_commute _ ?_ ?_
  · intro A hA
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hA
    exact Ch1.charTwo_map_mulEquiv (MulAut.conj (s : G)) hKc
  · intro A hA B hB hAB a ha b hb
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB
    have hLs := isComponentIn_map_conj hL (hSH s.2)
    have hLt := isComponentIn_map_conj hL (hSH t.2)
    have ha' : a ∈ K.map (MulAut.conj (s : G)).toMonoidHom := ha
    have hb' : b ∈ K.map (MulAut.conj (t : G)).toMonoidHom := hb
    rcases BenderBranch.eq_or_commute_of_isComponentIn hLs hLt with h | h
    · exact absurd (map_conj_eq_of_map_conj_eq hK s.2 t.2 h) hAB
    · exact BenderBranch.commute_of_commutator_eq_bot h
        (Subgroup.map_mono hKL ha') (Subgroup.map_mono hKL hb')

end Components

end CFSG.QuasithinUnique.Unc25G2

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Overgroup

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem Tuple25.le_M_of_component_charTwo (hs : UnconstrainedSetting G T M)
    (ht : Tuple25 T M H S z) {L K : Subgroup G} (hL : IsComponentIn L H) (hKL : K ≤ L)
    (hK : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hKc : CharTwo K) : K ≤ M := by
  have hcj : CharTwo (conjJoin S K) :=
    Unc25G2.charTwo_conjJoin_of_component ht.le_H hL hKL hK hKc
  have hX : CharTwo (conjJoin S K ⊔ S) :=
    Unc25G2.charTwo_sup_of_isPGroup_le_normalizer hcj ht.sylow.2.1 (le_normalizer_conjJoin S K)
  have hM : conjJoin S K ⊔ S ≤ M := ht.le_M_of_charTwo hs le_sup_right hX
  refine le_trans ?_ (le_sup_left.trans hM)
  refine le_trans ?_ (le_iSup _ (⟨1, S.one_mem⟩ : S))
  intro y hy
  exact ⟨y, hy, by simp⟩

end Overgroup

end CFSG.QuasithinUnique
