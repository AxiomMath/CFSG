module

public import CFSG.Goldschmidt75.TheoremBa
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D23

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem mem_closure_omegaOne_iff {W : Subgroup G} (hW : IsMulCommutative W) {x : G} :
    x ∈ closure (omegaOne W) ↔ x ∈ omegaOne W := by
  constructor
  · intro hx
    have hle : closure (omegaOne W) ≤ W := (closure_le _).mpr fun y hy => hy.1
    exact ⟨hle hx, mul_self_eq_one_of_mem_closure hle hW
      (fun y hy => by rw [pow_two]; exact hy.2) hx⟩
  · exact fun hx => subset_closure hx

omit [Finite G] in
theorem exists_not_commute_of_mem_of_not_connected {X : Type} [Group X] {E : Set X}
    (hE : ¬ (CFSG.Fischer.commGraph E).Connected) {d : X} (hd : d ∈ E) :
    ∃ e ∈ E, d * e ≠ e * d := by
  by_contra hcon
  push Not at hcon
  apply hE
  have hreach : ∀ u : E, (CFSG.Fischer.commGraph E).Reachable u ⟨d, hd⟩ := by
    intro u
    rcases eq_or_ne u ⟨d, hd⟩ with hu | hu
    · subst hu
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ⟨hu, (hcon u u.2).symm⟩
  have : Nonempty E := ⟨⟨d, hd⟩⟩
  exact ⟨fun u v => (hreach u).trans (hreach v).symm⟩

theorem exists_mul_mem_normalizer_of_mem_normalizer (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {Z : Subgroup G} (hZW : Z ≤ sec4W Ω S) {n : G}
    (hn : n ∈ normalizer (Z : Set G)) :
    ∃ c ∈ centralizer (Z : Set G), n * c ∈ normalizer (sec4W Ω S : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWC : W ≤ centralizer (Z : Set G) := fun w hw =>
    mem_centralizer_iff.mpr fun z hz => sec4W_mul_comm hΩ hS (hZW hz) hw
  have hWnC : AschbacherTightEmbedding.rightConjugate W n ≤ centralizer (Z : Set G) := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    refine mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : n * z * n⁻¹ ∈ Z := (mem_normalizer_iff.mp hn z).mp hz
    have h1 := sec4W_mul_comm hΩ hS (hZW hz') hy
    have h2 : n * (z * y) * n⁻¹ = n * (y * z) * n⁻¹ := by
      calc n * (z * y) * n⁻¹ = (n * z * n⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * y * n⁻¹) * (n * z * n⁻¹) := h1
        _ = n * (y * z) * n⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨Q₁, hQ₁, hWQ₁⟩ := exists_isSylowOf_le hW2 hWC
  obtain ⟨Q₂, hQ₂, hWnQ₂⟩ :=
    exists_isSylowOf_le (hW2.map _ : IsPGroup 2 (AschbacherTightEmbedding.rightConjugate W n))
      hWnC
  obtain ⟨c, hcC, hc⟩ := L26.IsSylowOf.exists_conj_mem hQ₁ hQ₂
  obtain ⟨S₁, hS₁, hQ₁S₁⟩ := exists_isSylowOf_le hQ₁.isPGroup (le_top : Q₁ ≤ ⊤)
  have hconj : AschbacherTightEmbedding.rightConjugate W (n * c) ≤ S₁ := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 : c * x * c⁻¹ ∈ AschbacherTightEmbedding.rightConjugate W n := by
      rw [mem_rightConjugate_iff]
      have e : n * (c * x * c⁻¹) * n⁻¹ = n * c * x * (n * c)⁻¹ := by group
      rw [e]
      exact hx
    have h2 := (hc _).mp (hWnQ₂ h1)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [e] at h2
    exact hQ₁S₁ h2
  have heq := rightConjugate_sec4W_eq_of_le hΩ hS hS₁ (hWQ₁.trans hQ₁S₁) hconj
  exact ⟨c, hcC, (rightConjugate_eq_self_iff W _).mp heq⟩

theorem centralizer_le_normalizer_of_mem_omegaD (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {Z : Subgroup G} (hZ : ∀ x ∈ sec4W Ω S, x * x = 1 → x ∈ Z)
    {L : Subgroup G} (hL : L ∈ omegaD Ω (sec4W Ω S)) :
    centralizer (Z : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLΩ, T, hT, hTW⟩ := hL
  intro c hc
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hLΩ hT
  obtain ⟨z, hzV, hz1, hzz, -, -⟩ := hV.exists_involution
  have hzZ : z ∈ Z := hZ z (rot_le_sec4W hΩ hS hLΩ hT hV hTW hzV) hzz
  apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hLΩ) (hT.le (hV.le hzV))
    hz1 hzz
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hc z hzZ).symm

theorem MinCounter.isSylowOf_inf_centralizer (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {Z : Subgroup G} (hZ : ∀ x ∈ sec4W Ω S, x * x = 1 → x ∈ Z) (hZW : Z ≤ sec4W Ω S)
    {L T V : Subgroup G} (hL : L ∈ Ω) (hT : IsSylowOf 2 T L)
    (hTW : T ≤ normalizer (sec4W Ω S : Set G)) (hV : IsDihedralRot V T) :
    IsSylowOf 2 V (L ⊓ centralizer (Z : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  set W := sec4W Ω S with hWdef
  have hVW : V ≤ W := rot_le_sec4W hΩ hS hL hT hV hTW
  have hV2 : IsPGroup 2 V := hT.isPGroup.to_le hV.le
  have hVC : V ≤ centralizer (Z : Set G) := fun v hv =>
    mem_centralizer_iff.mpr fun z hz => sec4W_mul_comm hΩ hS (hZW hz) (hVW hv)
  obtain ⟨P, hP, hVP⟩ := exists_isSylowOf_le hV2 (le_inf (hV.le.trans hT.le) hVC)
  have hTD : T ∈ DSet Ω W := ⟨⟨L, hL, hT⟩, hTW⟩
  obtain ⟨d, hd⟩ := IsBarOf.exists_of_mem hΩ hTD
  obtain ⟨e, he, hde⟩ :=
    exists_not_commute_of_mem_of_not_connected hdis (IsBarOf.mem_dBar hTD hd)
  obtain ⟨T'', ⟨⟨L'', hL'', hT''⟩, hT''W⟩, he''⟩ := DBar.exists_isBarOf he
  have hLL'' : L ≠ L'' := by
    rintro rfl
    exact hde (by rw [bar_eq_of_same H hS hL hT hT'' hTW hT''W hd he''])
  have hPV : P = V := by
    by_contra hne
    obtain ⟨T', hT', hPT'⟩ := exists_isSylowOf_le hP.isPGroup (hP.le.trans inf_le_left)
    obtain ⟨V', hV'⟩ := Assumption41.exists_rot hΩ hL hT'
    have hVT' : V ≤ T' := hVP.trans hPT'
    have hidx : V.relIndex T' = 2 := by
      have h1 := Subgroup.relIndex_mul_card V T'
      rw [inf_eq_left.mpr hVT', Assumption41.card_sylow_eq hΩ hL hL hT' hT, hV.card_eq] at h1
      have hpos : 0 < Nat.card V := Nat.card_pos
      have h2 : V.relIndex T' * Nat.card V = 2 * Nat.card V := h1
      exact Nat.eq_of_mul_eq_mul_right hpos h2
    have hVeq : V = V' := hV'.eq_of_isCyclic hVT' hV.isCyclic hidx
    rw [← hVeq] at hV'
    obtain ⟨p, hpP, hpV⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hVP (Ne.symm hne))
    have hT'P : T' ≤ P := by
      intro y hy
      by_cases hyV : y ∈ V
      · exact hVP hyV
      · have hpinv : p⁻¹ ∉ V := fun h => hpV (by simpa using inv_mem h)
        have h1 : p⁻¹ * y ∈ V := hV'.mul_mem_of_not_mem (inv_mem (hPT' hpP)) hy hpinv hyV
        have e : y = p * (p⁻¹ * y) := by group
        rw [e]
        exact mul_mem hpP (hVP h1)
    have hT'N : T' ≤ normalizer (L'' : Set G) := fun y hy =>
      centralizer_le_normalizer_of_mem_omegaD hΩ hS hZ ⟨hL'', T'', hT'', hT''W⟩
        (mem_inf.mp (hP.le (hT'P hy))).2
    obtain ⟨h1, h2⟩ := le_normalizer_of_sylow h22 hΩ hL'' hL (Ne.symm hLL'') hT' hT'N
    exact hde (bar_commute_of_sylow H hS hL hL'' hLL'' hT hT'' hTW h2 h1 hd he'')
  rw [← hPV]
  exact hP

theorem MinCounter.exists_oddCoreIn_conj_rot (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {Z : Subgroup G} (hZ : ∀ x ∈ sec4W Ω S, x * x = 1 → x ∈ Z) (hZW : Z ≤ sec4W Ω S)
    {L T V : Subgroup G} (hL : L ∈ Ω) (hT : IsSylowOf 2 T L)
    (hTW : T ≤ normalizer (sec4W Ω S : Set G)) (hV : IsDihedralRot V T) {c : G}
    (hc : c ∈ centralizer (Z : Set G)) :
    ∃ o ∈ oddCoreIn (centralizer (Z : Set G)), ∀ v ∈ V, o * (c * v * c⁻¹) * o⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set C := centralizer (Z : Set G) with hCdef
  set B := L ⊓ C with hBdef
  have hVB := hM.isSylowOf_inf_centralizer h22 hdis hZ hZW hL hT hTW hV
  have hV2 : IsPGroup 2 V := hVB.isPGroup
  have hCL : C ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_mem_omegaD hΩ hS hZ ⟨hL, T, hT, hTW⟩
  have hCB : C ≤ normalizer (B : Set G) := fun x hx =>
    inf_le_normalizer_inf (mem_inf.mpr ⟨hCL hx, le_normalizer hx⟩)
  set P := AschbacherTightEmbedding.rightConjugate V c⁻¹ with hPdef
  have hmemP : ∀ v ∈ V, c * v * c⁻¹ ∈ P := fun v hv => by
    rw [hPdef, mem_rightConjugate_iff, inv_inv]
    have e : c⁻¹ * (c * v * c⁻¹) * c = v := by group
    rw [e]
    exact hv
  have hPB : P ≤ B := by
    intro y hy
    rw [hPdef, mem_rightConjugate_iff, inv_inv] at hy
    have h1 := (mem_normalizer_iff.mp (hCB hc) _).mp (hVB.le hy)
    have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
    rwa [e] at h1
  have hP2 : IsPGroup 2 P := hV2.map _
  have hALB : oddCoreIn L ⊓ C ≤ oddCoreIn B := by
    refine le_oddCoreIn_of_le_normalizer (le_inf (inf_le_left.trans (oddCoreIn_le L))
      inf_le_right) (fun x hx => ?_)
      ((odd_card_oddCoreIn L).of_dvd_nat (card_dvd_of_le inf_le_left))
    exact inf_le_normalizer_inf (mem_inf.mpr
      ⟨normalizer_le_normalizer_oddCoreIn L (le_normalizer (mem_inf.mp hx).1),
        le_normalizer (mem_inf.mp hx).2⟩)
  have hBbar : IsPGroup 2 (imgOf B B) := by
    rintro ⟨_, b, -, rfl⟩
    have hbL : (b : G) ∈ L := (mem_inf.mp b.2).1
    have hbC : (b : G) ∈ C := (mem_inf.mp b.2).2
    obtain ⟨o, ho, r, hr, hbor⟩ := hM.twoNil L hL T hT b hbL
    obtain ⟨k, hk⟩ := hT.isPGroup ⟨r, hr⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨o', ho', hpow⟩ := exists_mul_pow_eq (le_normalizer_oddCoreIn L (hT.le hr)) ho (2 ^ k)
    have hbk : (b : G) ^ 2 ^ k ∈ oddCoreIn L ⊓ C := by
      refine mem_inf.mpr ⟨?_, pow_mem hbC _⟩
      rw [hbor, hpow, hrk, mul_one]
      exact ho'
    obtain ⟨y, hy, hye⟩ := hALB hbk
    refine ⟨k, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (CFSG.Assembly.oddCore B) b) ^ 2 ^ k = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hyb : y = b ^ 2 ^ k := Subtype.ext (by simpa using hye)
    rw [← hyb]
    exact hy
  have himg : imgOf B P ≤ imgOf B V := by
    have hVs := isSylowOf_imgOf hVB le_rfl
    rw [imgOf_self] at hVs
    have hBbar' : IsPGroup 2 (⊤ : Subgroup (B ⧸ CFSG.Assembly.oddCore B)) := by
      rw [← imgOf_self B]
      exact hBbar
    have heq := hVs.eq_of_le le_top le_rfl hBbar'
    rw [← heq]
    exact le_top
  obtain ⟨o, ho, hoP⟩ := exists_conj_le_of_imgOf_le hPB hV2 hP2 himg
  have hOB : oddCoreIn B ≤ oddCoreIn C :=
    le_oddCoreIn_of_le_normalizer ((oddCoreIn_le B).trans inf_le_right)
      (hCB.trans (normalizer_le_normalizer_oddCoreIn B)) (odd_card_oddCoreIn B)
  exact ⟨o, hOB ho, fun v hv => hoP _ (hmemP v hv)⟩

theorem MinCounter.conj_mem_sup_oddCoreIn_centralizer (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {Z : Subgroup G} (hZ : ∀ x ∈ sec4W Ω S, x * x = 1 → x ∈ Z) (hZW : Z ≤ sec4W Ω S) {c : G}
    (hc : c ∈ centralizer (Z : Set G)) {w : G} (hw : w ∈ sec4W Ω S) :
    c * w * c⁻¹ ∈ sec4W Ω S ⊔ oddCoreIn (centralizer (Z : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  set Y := W ⊔ oddCoreIn (centralizer (Z : Set G)) with hYdef
  have hle : AschbacherTightEmbedding.rightConjugate W c⁻¹ ≤ Y := by
    rw [rightConjugate_le_iff]
    refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
    rw [← rightConjugate_le_iff]
    obtain ⟨L, hL, T₀, hT₀, hU₀⟩ := IsRot.exists_isDihedralRot hΩ hU
    obtain ⟨T, hT, hUT, hTW⟩ :=
      exists_isSylowOf_le_normalizer_of_isRot hΩ hS hL hT₀ hU₀ (le_sec4W hUS hU)
    obtain ⟨o, ho, hoU⟩ := hM.exists_oddCoreIn_conj_rot h22 hdis hZ hZW hL hT hTW hUT hc
    have hUW : U ≤ W := rot_le_sec4W hΩ hS hL hT hUT hTW
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have h1 := hoU _ hy
    have hoY : o ∈ Y := mem_sup_right ho
    have e : y = o⁻¹ * (o * (c * (c⁻¹ * y * c) * c⁻¹) * o⁻¹) * o := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hoY) (mem_sup_left (hUW h1))) hoY
  apply hle
  rw [mem_rightConjugate_iff, inv_inv]
  have e : c⁻¹ * (c * w * c⁻¹) * c = w := by group
  rw [e]
  exact hw

theorem MinCounter.sec4W_stronglyClosed (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    (hZcl : ∀ v ∈ omegaOne (sec4W Ω S), ∀ g : G, g⁻¹ * v * g ∈ S →
      g⁻¹ * v * g ∈ omegaOne (sec4W Ω S)) :
    ∀ w ∈ sec4W Ω S, ∀ g : G, g⁻¹ * w * g ∈ S → g⁻¹ * w * g ∈ sec4W Ω S := by
  intro w hw g hwg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWab : IsMulCommutative W := isMulCommutative_sec4W hΩ hS.isPGroup
  set Z := closure (omegaOne W) with hZdef
  have hZiff : ∀ x, x ∈ Z ↔ x ∈ omegaOne W := fun x => mem_closure_omegaOne_iff hWab
  have hZW : Z ≤ W := fun x hx => ((hZiff x).mp hx).1
  have hZ : ∀ x ∈ W, x * x = 1 → x ∈ Z := fun x hx hxx => (hZiff x).mpr ⟨hx, hxx⟩
  obtain ⟨P₀, hP₀⟩ := Asc76X.exists_sylow_eq_of_isSylowOf_top hS
  have hZP₀ : Z ≤ (P₀ : Subgroup G) := hP₀ ▸ hZW.trans (sec4W_le S)
  have hZsc : CFSG.Open.fusionStronglyClosed (Z : Set G) P₀ := by
    intro a ha x hx
    have hx' : x⁻¹ * a * x ∈ S := by rw [← hP₀]; exact hx
    exact (hZiff _).mpr (hZcl a ((hZiff a).mp ha) x hx')
  have hU₁ : ({w} : Set G) ⊆ (P₀ : Set G) := by
    rw [Set.singleton_subset_iff]
    show w ∈ (P₀ : Subgroup G)
    rw [hP₀]
    exact sec4W_le S hw
  have hU₂ : ({g⁻¹ * w * g} : Set G) ⊆ (P₀ : Set G) := by
    rw [Set.singleton_subset_iff]
    show g⁻¹ * w * g ∈ (P₀ : Subgroup G)
    rw [hP₀]
    exact hwg
  obtain ⟨n, hn, hneq⟩ := CFSG.Goldschmidt75.theoremB_a P₀ hZP₀ hZsc hU₁ hU₂ (g := g)
    (by simp)
  have hmem : g⁻¹ * w * g ∈ (fun x => n⁻¹ * x * n) '' ((Z : Set G) * ({w} : Set G)) := by
    rw [hneq]
    have h1 := Set.mul_mem_mul (show (1 : G) ∈ (Z : Set G) from Z.one_mem)
      (show g⁻¹ * w * g ∈ ({g⁻¹ * w * g} : Set G) from Set.mem_singleton _)
    rwa [one_mul] at h1
  obtain ⟨y, hy, hyeq⟩ := hmem
  obtain ⟨ζ, hζ, w', hw', rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  obtain ⟨c, hcC, hncW⟩ := exists_mul_mem_normalizer_of_mem_normalizer hΩ hS hZW hn
  set w₁ := (n * c)⁻¹ * w' * (n * c) with hw₁def
  have hw₁ : w₁ ∈ W := by
    have := (mem_normalizer_iff.mp (inv_mem hncW) w').mp hw
    simpa [hw₁def, mul_assoc] using this
  have hcw := hM.conj_mem_sup_oddCoreIn_centralizer h22 hdis hZ hZW hcC hw₁
  set Y := W ⊔ oddCoreIn (centralizer (Z : Set G)) with hYdef
  have hζ' : n⁻¹ * ζ * n ∈ Z := by
    have := (mem_normalizer_iff.mp (inv_mem hn) ζ).mp hζ
    simpa using this
  have hgY : g⁻¹ * w' * g ∈ Y := by
    rw [← hyeq]
    show n⁻¹ * (ζ * w') * n ∈ Y
    have e : n⁻¹ * (ζ * w') * n = (n⁻¹ * ζ * n) * (c * w₁ * c⁻¹) := by rw [hw₁def]; group
    rw [e]
    exact mul_mem (mem_sup_left (hZW hζ')) hcw
  have hWO : W ≤ normalizer (oddCoreIn (centralizer (Z : Set G)) : Set G) := by
    intro x hx
    apply le_normalizer_oddCoreIn
    exact mem_centralizer_iff.mpr fun z hz => sec4W_mul_comm hΩ hS (hZW hz) hx
  have hsyl : IsSylowOf 2 W Y :=
    isSylowOf_sup_of_odd_of_le_normalizer hW2 (odd_card_oddCoreIn _) hWO
  have heq := hsyl.eq_of_le (le_inf le_sup_left (sec4W_le S)) inf_le_left
    (hS.isPGroup.to_le inf_le_right)
  rw [← heq]
  exact mem_inf.mpr ⟨hgY, hwg⟩

end CFSG.ComponentClassification.Asc76.Sec4
