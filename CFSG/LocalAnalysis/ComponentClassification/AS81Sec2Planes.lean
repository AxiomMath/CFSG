module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2F0Plane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover LinearFlag

variable {G : Type} [Group G] [Finite G]

namespace Sec2

theorem mem_or_mem_of_sq_eq_one {A T H₁ H₂ : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) (hTsyl : IsSylowOf 2 T A)
    (hH₁ : H₁ ≤ T) (hH₁e : IsElemAbelian 2 H₁) (hH₁16 : Nat.card H₁ = 16)
    (hH₂ : H₂ ≤ T) (hH₂e : IsElemAbelian 2 H₂) (hH₂16 : Nat.card H₂ = 16) (hne : H₁ ≠ H₂)
    {t : G} (ht : t ∈ T) (ht2 : t ^ 2 = 1) : t ∈ H₁ ∨ t ∈ H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  obtain ⟨φ, -, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hrad : ∀ X : Subgroup G, X ≤ T → IsElemAbelian 2 X → Nat.card X = 16 →
      ∃ i : Fin 2, (X.subgroupOf A).map φ = projRad c.k i := by
    intro X hXT hX hX16
    have hX₀T : X.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hXT (mem_subgroupOf.mp hx))
    have hX₀ : IsPGroup 2 (X.subgroupOf A) := hT₀2.to_le hX₀T
    have h2 : ∀ x ∈ (X.subgroupOf A).map φ, x ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hX.2 _ (mem_subgroupOf.mp hx)),
        map_one]
    have h16 : Nat.card ((X.subgroupOf A).map φ) = 16 := by
      rw [card_map_of_isPGroup φ hkerodd hX₀, ← hX16]
      exact Nat.card_congr (subgroupOfEquivOfLe (hXT.trans hTA)).toEquiv
    have hU : (X.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hX₀T
    rcases eq_projRad_of_le_projUnip c.card_k hU h2 h16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hinj : ∀ X Y : Subgroup G, X ≤ T → Y ≤ T →
      (X.subgroupOf A).map φ = (Y.subgroupOf A).map φ → X = Y := by
    have key : ∀ X Y : Subgroup G, X ≤ T → Y ≤ T →
        (X.subgroupOf A).map φ ≤ (Y.subgroupOf A).map φ → X ≤ Y := by
      intro X Y hXT hYT h x hx
      have hxA : x ∈ A := hTA (hXT hx)
      obtain ⟨y, hy, hyx⟩ := h ⟨⟨x, hxA⟩, hx, rfl⟩
      have hyT₀ : y ∈ (T₀ : Subgroup ↥A) := hTsub ▸ (hYT (mem_subgroupOf.mp hy))
      have hxT₀ : (⟨x, hxA⟩ : ↥A) ∈ (T₀ : Subgroup ↥A) := hTsub ▸ (hXT hx)
      rw [eq_of_map_eq_of_isPGroup φ hkerodd hT₀2 hyT₀ hxT₀ hyx] at hy
      exact hy
    exact fun X Y hXT hYT h => le_antisymm (key X Y hXT hYT h.le) (key Y X hYT hXT h.ge)
  obtain ⟨i₁, hi₁⟩ := hrad H₁ hH₁ hH₁e hH₁16
  obtain ⟨i₂, hi₂⟩ := hrad H₂ hH₂ hH₂e hH₂16
  have hi₁₂ : i₁ ≠ i₂ := fun h => hne (hinj H₁ H₂ hH₁ hH₂ (by rw [hi₁, hi₂, h]))
  have htA : t ∈ A := hTA ht
  have htT₀ : (⟨t, htA⟩ : ↥A) ∈ (T₀ : Subgroup ↥A) := hTsub ▸ ht
  have hφt : φ ⟨t, htA⟩ ∈ projUnip c.k := hφT ▸ ⟨_, htT₀, rfl⟩
  have hφt2 : φ ⟨t, htA⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨t, htA⟩ : ↥A) ^ 2 = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hmem : ∀ i : Fin 2, ∀ X : Subgroup G, X ≤ T → (X.subgroupOf A).map φ = projRad c.k i →
      φ ⟨t, htA⟩ ∈ projRad c.k i → t ∈ X := by
    intro i X hXT hX hti
    rw [← hX] at hti
    obtain ⟨x, hx, hxt⟩ := hti
    have hxT₀ : x ∈ (T₀ : Subgroup ↥A) := hTsub ▸ (hXT (mem_subgroupOf.mp hx))
    rw [eq_of_map_eq_of_isPGroup φ hkerodd hT₀2 hxT₀ htT₀ hxt] at hx
    exact hx
  have hfin : ∀ a b c : Fin 2, b ≠ c → a = b ∨ a = c := by decide
  have hj : ∃ j : Fin 2, φ ⟨t, htA⟩ ∈ projRad c.k j := by
    rcases mem_projRad_of_sq_eq_one c.card_k hφt hφt2 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨j, hjt⟩ := hj
  rcases hfin j i₁ i₂ hi₁₂ with rfl | rfl
  · exact Or.inl (hmem _ H₁ hH₁ hi₁ hjt)
  · exact Or.inr (hmem _ H₂ hH₂ hi₂ hjt)

end Sec2

omit [Finite G] in
theorem planes_comm (E F : Subgroup G) : planes F E = planes E F := by
  ext V
  exact ⟨fun ⟨h, hV⟩ => ⟨h, hV.symm⟩, fun ⟨h, hV⟩ => ⟨h, hV.symm⟩⟩

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem mem_or_mem_of_mul_self_eq_one_of_odd_center (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {s : G} (hs : s ∈ E ⊔ F)
    (hs2 : s * s = 1) :
    s ∈ E ∨ s ∈ F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  obtain ⟨hRD, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hF.sylow.le hs
  have htr : t * r = r * t := mem_centralizer_iff.mp (hRA hr) t ht.2
  have hr2 : r * r = 1 := by rw [← sq]; exact hF.elemR.2 r hr
  have ht2 : t ^ 2 = 1 := by
    have h : t * r * (t * r) = t * t * (r * r) := by
      calc t * r * (t * r) = t * (r * t) * r := by group
        _ = t * (t * r) * r := by rw [htr]
        _ = t * t * (r * r) := by group
    rw [h, hr2, mul_one] at hs2
    rw [sq, hs2]
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
  have hne : E ⊓ A ≠ F ⊓ A := fun h => hF.ne (by rw [hEeq, hFeq, h])
  rcases Sec2.mem_or_mem_of_sq_eq_one hF.quasisimple hL hodd hTsyl
    (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    (card_inf_left hF hodd)
    (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
    (card_inf_left hF.symm hodd) hne ht ht2 with h | h
  · exact Or.inl (E.mul_mem h.1 (hF.R_le_E hr))
  · exact Or.inr (F.mul_mem h.1 (hF.R_le_F hr))

theorem isElemAbelian_and_card_of_mem_planes (hF : Frame G A A R g E F) {V : Subgroup G}
    (hV : V ∈ planes E F) : IsElemAbelian 2 V ∧ Nat.card V = 64 := by
  obtain ⟨h, rfl | rfl⟩ := hV
  · exact ⟨AS76b.isElemAbelian_rightConjugate hF.elemE h, by rw [rightConjugate_card, hF.cardE]⟩
  · exact ⟨AS76b.isElemAbelian_rightConjugate hF.elemF h, by rw [rightConjugate_card, hF.cardF]⟩

theorem mem_of_mem_centralizer_of_mem_planes (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {V : Subgroup G}
    (hV : V ∈ planes E F) {c : G} (hc : c ∈ centralizer (V : Set G)) {n : ℕ}
    (hcn : c ^ 2 ^ n = 1) : c ∈ V := by
  have key : ∀ {W : Subgroup G}, (∀ c ∈ centralizer (W : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ W) →
      ∀ h : G, c ∈ centralizer (rightConjugate W h : Set G) → c ∈ rightConjugate W h := by
    intro W hW h hch
    rw [mem_rightConjugate_iff]
    refine hW _ (mem_centralizer_iff.mpr fun w hw => ?_) n (by rw [conj_pow, hcn]; group)
    have h1 := mem_centralizer_iff.mp hch (h⁻¹ * w * h)
      ((mem_rightConjugate_iff W h _).mpr (by group; exact hw))
    calc w * (h * c * h⁻¹) = h * ((h⁻¹ * w * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * w * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * w := by group
  obtain ⟨h, rfl | rfl⟩ := hV
  · exact key (mem_of_mem_centralizer_of_frame hF hL hodd) h hc
  · exact key (mem_of_mem_centralizer_of_frame hF.symm hL hodd) h hc

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem sec2S_le_normalizer_of_sec2Z_le {V : Subgroup G} (hZV : sec2Z A E F ≤ V)
    (hVS : V ≤ sec2S A R E F) : sec2S A R E F ≤ normalizer (V : Set G) := fun s hs =>
  Sec2.mem_normalizer_of_forall_conj_mem fun v hv => by
    have h := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd hs (hVS hv)).2
    have : s * v * s⁻¹ = (s * v * s⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem (hZV h) hv

theorem sec2Z_le_of_mem_planes {V : Subgroup G} (hV : V ∈ planes E F)
    (hVS : V ≤ sec2S A R E F) : sec2Z A E F ≤ V := by
  intro z hz
  have hz2 : z ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    rw [hF.sec2Z_eq] at hz
    exact hF.elemE.2 z hz.1.1
  rw [← centerIn_sec2S_eq h11 hE16 hF hL hodd] at hz
  exact mem_of_mem_centralizer_of_mem_planes hF hL hodd hV
    (Subgroup.centralizer_le hVS (mem_inf.mp hz).2) hz2

theorem mem_of_mem_F_of_commute {f e : G} (hf : f ∈ F) (he : e ∈ E ⊓ A)
    (heZ : e ∉ sec2Z A E F) (hfe : f * e = e * f) : f ∈ E := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hF.sylowR.le hF.sylowR.isPGroup hodd
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hREF : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  set u := e * r with hu
  have huE : u ∈ E := E.mul_mem he.1 (hF.R_le_E hr)
  have huA : u ∉ E ⊓ A := fun h => hr1 (by
    have h1 : r ∈ R ⊓ A := ⟨hr, by simpa [hu] using A.mul_mem (A.inv_mem he.2) h.2⟩
    rwa [hRA1, mem_bot] at h1)
  obtain ⟨Q, hQ, huQ⟩ := hD.cover u huE huA
  have hQEF : ¬ Q ≤ E ⊓ F := fun h => heZ (by
    have h1 : e ∈ E ⊓ F := by simpa [hu] using (E ⊓ F).mul_mem (h huQ) ((E ⊓ F).inv_mem (hREF hr))
    rw [hF.sec2Z_eq]
    exact ⟨h1, he.2⟩)
  have hfu : f * u * f⁻¹ = u := by
    have hfr : f * r = r * f := hFc f hf r (hF.R_le_F hr)
    rw [hu, ← mul_assoc, hfe, mul_assoc e f r, hfr, ← mul_assoc, mul_inv_cancel_right]
  have hfN := hF.F_le_normalizer hL hodd hf
  have hQf : rightConjugate Q f = Q := by
    by_contra hne
    have hmem : u ∈ rightConjugate Q f ⊓ Q :=
      ⟨(mem_rightConjugate_iff Q f u).mpr (by rw [hfu]; exact huQ), huQ⟩
    rw [hD.disj _ (rightConjugate_mem_pointsIn hQ hfN) _ hQ hne, mem_bot] at hmem
    exact huA (hmem ▸ (E ⊓ A).one_mem)
  exact mem_of_mem_normalizer_of_not_le h11 hE16 hF hL hodd hf hQ hQEF
    ((rightConjugate_eq_self_iff Q f).mp hQf)

omit h11 hE16 in
theorem F_le_normalizer_centralizerMod :
    F ≤ normalizer (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) : Set G) :=
  fun f hf => by
    have hfE := hF.F_le_normalizer hL hodd hf
    have hfF : f ∈ normalizer (F : Set G) := le_normalizer hf
    have hfA : f ∈ normalizer (A : Set G) :=
      sup_le_normalizer_left hF.sylowR.le (hF.F_le hf)
    have hfEF : f ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hfE, hfF⟩
    have hfZ : f ∈ normalizer (sec2Z A E F : Set G) := by
      rw [hF.sec2Z_eq]
      exact inf_normalizer_le_normalizer_inf ⟨hfEF, hfA⟩
    have hfRZ : f ∈ normalizer ((R ⊔ sec2Z A E F : Subgroup G) : Set G) := by
      rw [hF.sup_sec2Z]
      exact hfEF
    exact Sec2.mem_normalizer_centralizerMod (Sec2.normalizer_le_normalizer_sec2P E hfE) hfRZ hfZ

theorem mem_centralizerMod_of_mem_sec2S_of_commute {s e : G} (hs : s ∈ sec2S A R E F)
    (he : e ∈ E ⊓ A) (heZ : e ∉ sec2Z A E F) (hse : s * e = e * s) :
    s ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hs' : s ∈ ((F ⊔ C : Subgroup G) : Set G) := hs
  rw [coe_mul_of_left_le_normalizer_right F C
    (F_le_normalizer_centralizerMod hF hL hodd)] at hs'
  obtain ⟨f, hf, c, hc, rfl⟩ := hs'
  have hce : c * e = e * c :=
    (mem_centralizer_iff.mp (hPC (mem_centralizerMod.mp hc).1) e he).symm
  have hfe : f * e = e * f := by
    have h1 : f * e * c = e * f * c := by
      calc f * e * c = f * (e * c) := by group
        _ = f * (c * e) := by rw [hce]
        _ = f * c * e := by group
        _ = e * (f * c) := hse
        _ = e * f * c := by group
    exact mul_right_cancel h1
  exact C.mul_mem (le_centralizerMod hF (mem_of_mem_F_of_commute h11 hE16 hF hL hodd hf he heZ hfe))
    hc

omit h11 hE16 hL hodd in
theorem le_sec2S_and_le_sec2S : E ≤ sec2S A R E F ∧ F ≤ sec2S A R E F :=
  ⟨(le_centralizerMod hF).trans le_sup_right, le_sup_left⟩

theorem eq_or_eq_of_le_sec2S_of_mem_inf {D : Subgroup G} (hD : IsElemAbelian 2 D)
    (hD64 : Nat.card D = 64) (hDS : D ≤ sec2S A R E F) {u : G} (huR : u ∈ R) (huD : u ∈ D)
    (hu1 : u ≠ 1) : D = E ∨ D = F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hS2 := (isSylowOf_sec2S h11 hE16 hF hL hodd).isPGroup
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  obtain ⟨c, hcK, hRcD, hDARc⟩ :=
    exists_rightConjugate_le_of_mem_inf_frame h11 hE16 hF hL hodd hD hD64 huR huD hu1
  have hSK : sec2S A R E F ⊓ centralizer (A : Set G) = R :=
    hR.eq_of_le (le_inf (hF.R_le_E.trans hES) hRA) inf_le_right (hS2.to_le inf_le_left)
  have hRcK : rightConjugate R c ≤ centralizer (A : Set G) := by
    have := AschbacherTheorem3.rightConjugate_le_rightConjugate hRA c
    rwa [(rightConjugate_eq_self_iff _ c).mpr (le_normalizer hcK)] at this
  have hRcR : rightConjugate R c ≤ R := by
    have := le_inf (hRcD.trans hDS) hRcK
    rwa [hSK] at this
  have hRc : rightConjugate R c = R :=
    eq_of_le_of_card_ge hRcR (by rw [rightConjugate_card])
  rw [hRc] at hRcD hDARc
  obtain ⟨-, hTsyl, -⟩ := sylow_sup_structure hRA hR.isPGroup hF.sylow
  have hSA : sec2S A R E F ⊓ A = (E ⊔ F) ⊓ A :=
    (hTsyl.eq_of_le (inf_le_inf_right A (sup_le hES hFS)) inf_le_right
      (hS2.to_le inf_le_left))
  have hDT : D ⊓ A ≤ (E ⊔ F) ⊓ A := hSA ▸ inf_le_inf_right A hDS
  have hDeq := eq_inf_sup_of_le_sup hRA hRcD hDARc
  have hDA16 : Nat.card (D ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hRcD hDARc hRA1
    rw [hD64, hF.cardR] at this
    omega
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  have hFeq := eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le
  have hne : E ⊓ A ≠ F ⊓ A := fun h => hF.ne (by rw [hEeq, hFeq, h])
  rcases Sec2.eq_or_eq_of_card_sixteen hF.quasisimple hL hodd hTsyl hDT
    (AS76b.IsElemAbelian.mono hD inf_le_left) hDA16
    (inf_le_inf_right A le_sup_left) (AS76b.IsElemAbelian.mono hF.elemE inf_le_left)
    (card_inf_left hF hodd)
    (inf_le_inf_right A le_sup_right) (AS76b.IsElemAbelian.mono hF.elemF inf_le_left)
    (card_inf_left hF.symm hodd) hne with h | h
  · exact Or.inl (by rw [hDeq, h, ← hEeq])
  · exact Or.inr (by rw [hDeq, h, ← hFeq])

theorem exists_mem_sec2P_eq_rightConjugate_F {V : Subgroup G} (hV : V ∈ planes E F)
    (hVS : V ≤ sec2S A R E F) (hVP : ¬ V ≤ sec2P E) {v : G} (hvV : v ∈ V) (hvE : v ∈ E)
    (hvZ : v ∉ sec2Z A E F) : ∃ p ∈ sec2P E, V = rightConjugate F p := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCP : centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) ≤ sec2P E :=
    fun c hc => (mem_centralizerMod.mp hc).1
  have hVEA : ∀ e ∈ V, e ∈ E ⊓ A → e ∈ sec2Z A E F := fun e heV he => by
    by_contra heZ
    exact hVP fun s hs => hCP (mem_centralizerMod_of_mem_sec2S_of_commute h11 hE16 hF hL hodd
      (hVS hs) he heZ (hVc s hs e heV))
  have hvA : v ∉ E ⊓ A := fun h => hvZ (hVEA v hvV h)
  obtain ⟨Q, hQ, hvQ⟩ := hD.cover v hvE hvA
  obtain ⟨j, hj, rfl⟩ := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd Q hQ
  have hjS := sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd ((sec2P E).inv_mem hj)
  have hV'S : rightConjugate V j⁻¹ ≤ sec2S A R E F := by
    rw [← (rightConjugate_eq_self_iff _ _).mpr hjS]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVS j⁻¹
  have hu : j * v * j⁻¹ ∈ R := (mem_rightConjugate_iff R j v).mp hvQ
  have huV : j * v * j⁻¹ ∈ rightConjugate V j⁻¹ := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hvV
  have hu1 : j * v * j⁻¹ ≠ 1 := fun h => hvZ (by
    have h' : j⁻¹ * (j * v * j⁻¹) * j = j⁻¹ * 1 * j := by rw [h]
    rw [show j⁻¹ * (j * v * j⁻¹) * j = v by group, show j⁻¹ * 1 * j = 1 by group] at h'
    rw [h']
    exact (sec2Z A E F).one_mem)
  have hVj : V = rightConjugate (rightConjugate V j⁻¹) j := by
    rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  rcases eq_or_eq_of_le_sec2S_of_mem_inf h11 hE16 hF hL hodd
    (AS76b.isElemAbelian_rightConjugate hVe j⁻¹) (by rw [rightConjugate_card, hV64]) hV'S hu huV
    hu1 with h | h
  · exfalso
    apply hVP
    rw [hVj, h, (rightConjugate_eq_self_iff E j).mpr (Sec2.sec2P_le E hj)]
    exact Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl
  · exact ⟨j, hj, by rw [hVj, h]⟩

theorem exists_mem_inf_not_mem_sec2Z {V : Subgroup G} (hV : V ∈ planes E F)
    (hVS : V ≤ sec2S A R E F) :
    (∃ v ∈ V, v ∈ E ∧ v ∉ sec2Z A E F) ∨ (∃ v ∈ V, v ∈ F ∧ v ∉ sec2Z A E F) := by
  by_contra hno
  push Not at hno
  obtain ⟨hnE, hnF⟩ := hno
  obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hZV := sec2Z_le_of_mem_planes h11 hE16 hF hL hodd hV hVS
  have hle : V ⊓ (E ⊔ F) ≤ sec2Z A E F := fun w hw => by
    rcases mem_or_mem_of_mul_self_eq_one_of_odd_center hF hL hodd hw.2
      (by rw [← sq]; exact hVe.2 w hw.1) with h | h
    · exact hnE w hw.1 h
    · exact hnF w hw.1 h
  have hEF : Nat.card (E ⊔ F : Subgroup G) = 256 := by
    have h := card_sup_mul_card_inf (H := E) (R := F) (hF.F_le_normalizer hL hodd)
    rw [hF.card_inf, hF.cardE, hF.cardF] at h
    omega
  have h1 := card_sup_mul_card_inf (H := V) (R := E ⊔ F)
    ((sup_le hES hFS).trans (sec2S_le_normalizer_of_sec2Z_le h11 hE16 hF hL hodd hZV hVS))
  have h2 : Nat.card (V ⊔ (E ⊔ F) : Subgroup G) ≤ 16 * 64 := by
    rw [← card_sec2S h11 hE16 hF hL hodd]
    exact card_le_of_le (sup_le hVS (sup_le hES hFS))
  have h3 : Nat.card (V ⊓ (E ⊔ F) : Subgroup G) ≤ 4 := by
    rw [← hF.card_sec2Z hodd]
    exact card_le_of_le hle
  rw [hV64, hEF] at h1
  have h4 : 64 * 256 ≤ 16 * 64 * 4 :=
    h1 ▸ Nat.mul_le_mul h2 h3
  omega

theorem mem_planes_sec2S_cases {V : Subgroup G} (hV : V ∈ planes E F) (hVS : V ≤ sec2S A R E F)
    {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E)
    (hhS : h ∉ sec2S A R E F) :
    (V = E ∨ V = sec2F0 A E x ∨ ∃ p ∈ sec2P E, V = rightConjugate F p) ∨
      (V = F ∨ V = sec2F0 A F h ∨ ∃ y ∈ sec2P F, V = rightConjugate E y) := by
  obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  rcases exists_mem_inf_not_mem_sec2Z h11 hE16 hF hL hodd hV hVS with
    ⟨v, hvV, hvE, hvZ⟩ | ⟨v, hvV, hvF, hvZ⟩
  · left
    by_cases hVP : V ≤ sec2P E
    · rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS (le_inf hVP hVS) hVe with
        h1 | h1
      · exact Or.inl (eq_of_le_of_card_ge h1 (by rw [hV64, hF.cardE]))
      · exact Or.inr (Or.inl (eq_of_le_of_card_ge h1
          (by rw [hV64, card_sec2F0 h11 hE16 hF hL hodd hx hxS])))
    · exact Or.inr (Or.inr
        (exists_mem_sec2P_eq_rightConjugate_F h11 hE16 hF hL hodd hV hVS hVP hvV hvE hvZ))
  · right
    have hV' : V ∈ planes F E := by rw [planes_comm]; exact hV
    have hVS' : V ≤ sec2S A R F E := hSc ▸ hVS
    have hhS' : h ∉ sec2S A R F E := hSc ▸ hhS
    by_cases hVP : V ≤ sec2P F
    · rcases le_or_le_of_isElemAbelian h11 hE16 hF.symm hL hodd hh hhS' (le_inf hVP hVS') hVe with
        h1 | h1
      · exact Or.inl (eq_of_le_of_card_ge h1 (by rw [hV64, hF.cardF]))
      · exact Or.inr (Or.inl (eq_of_le_of_card_ge h1
          (by rw [hV64, card_sec2F0 h11 hE16 hF.symm hL hodd hh hhS'])))
    · exact Or.inr (Or.inr (exists_mem_sec2P_eq_rightConjugate_F h11 hE16 hF.symm hL hodd hV'
        hVS' hVP hvV hvF (by rw [sec2Z_comm]; exact hvZ)))

end Frame

end CFSG.ComponentClassification.AS81
