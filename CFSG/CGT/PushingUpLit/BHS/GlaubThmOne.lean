module

public import CFSG.CGT.PushingUpLit.BHS.GlaubOne
public import CFSG.CGT.PushingUpLit.BHS.GlaubSylow

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.CGT.PushingUpLit.BHS.Glauberman

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace Glauberman

theorem isPGroup_two_of_sq_eq_one {Γ : Type*} [Group Γ] {H : Subgroup Γ}
    (h : ∀ g ∈ H, g ^ 2 = 1) : IsPGroup 2 H := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using h (g : Γ) g.2)⟩

variable {V : Type*} [CommGroup V]

theorem sup_inf_eq_left_of_le {U₁ U₂ F₁ F₂ : Subgroup V} (h1 : U₁ ≤ F₁) (h2 : U₂ ≤ F₂)
    (h : F₁ ⊓ F₂ = ⊥) : (U₁ ⊔ U₂) ⊓ F₁ = U₁ := by
  apply le_antisymm
  · rintro x ⟨hx, hxF⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    have hzF : z ∈ F₁ := by
      have : z = y⁻¹ * (y * z) := by group
      rw [this]
      exact F₁.mul_mem (F₁.inv_mem (h1 hy)) hxF
    have hz0 : z ∈ F₁ ⊓ F₂ := ⟨hzF, h2 hz⟩
    rw [h] at hz0
    have hz1 : z = 1 := hz0
    simpa [hz1] using hy
  · exact fun x hx => ⟨Subgroup.mem_sup_left hx, h1 hx⟩

theorem card_commV_map_conj (k : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (commV (A.map (MulAut.conj k).toMonoidHom)) = Nat.card (commV A) := by
  rw [B19.commV_map_conj]
  exact Subgroup.card_map_of_injective (f := k.toMonoidHom) k.injective

theorem apply_mem_commV_of_mem {G : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ G) {x : V}
    (hx : x ∈ commV G) : g x ∈ commV G :=
  G6.apply_mem_commV (fun _ hy => G.mul_mem (G.mul_mem hg hy) (G.inv_mem hg)) hx

end Glauberman

variable {V : Type*} [CommGroup V]

namespace GlHyp

variable [Finite V] {G M S A : Subgroup (MulAut V)}

theorem isSylowOf_G (h : GlHyp G M S A) : IsSylowOf 2 S G := by
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_ge (K := G) h.syl.2.1 (h.syl.1.trans h.lt.le)
  by_cases hTS : T ≤ S
  · have hTS' : T = S := le_antisymm hTS hST
    rwa [hTS'] at hT
  · exfalso
    obtain ⟨t, htT, htS⟩ := IsConcreteLE.not_le_iff_exists.1 hTS
    have htM : t ∉ M := by
      intro htM
      have hle : T ⊓ M ≤ S := le_of_isSylowOf_of_le h.syl (hT.2.1.to_le inf_le_left)
        (le_inf hST h.syl.1) inf_le_right
      exact htS (hle ⟨htT, htM⟩)
    have hG := h.gen t (hT.1 htT) htM
    have hGT : G ≤ T := by
      rw [← hG]
      exact sup_le (h.le.trans hST) ((Subgroup.zpowers_le).2 htT)
    have hG2 : IsPGroup 2 G := hT.2.1.to_le hGT
    have hGcore : G ≤ pCoreOf 2 G :=
      le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hG2
    rw [h.o2] at hGcore
    exact h.ne (le_bot_iff.1 (h.A_le_G.trans hGcore))

theorem coreIn_inf_eq_bot (h : GlHyp G M S A) : coreIn G M ⊓ S = ⊥ := by
  have hSyl := h.isSylowOf_G
  have hNG : G ≤ Subgroup.normalizer (coreIn G M : Set (MulAut V)) := le_normalizer_coreIn G M
  obtain ⟨g, hgG, hgM⟩ := IsConcreteLE.exists_of_lt h.lt
  obtain ⟨x, hxN, hxG, y, hyN, rfl⟩ :=
    exists_mem_normalizer_mul hNG hSyl.1 hSyl.2.1 hSyl.2.2 hgG
  have hxM : x ∉ M := fun hxM => hgM (M.mul_mem hxM (coreIn_le hyN))
  have hgen := h.gen x hxG hxM
  have hAN : A ≤ Subgroup.normalizer ((S ⊓ coreIn G M : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (h.le ha), hNG (h.A_le_G ha)⟩
  have hGN : G ≤ Subgroup.normalizer ((S ⊓ coreIn G M : Subgroup (MulAut V)) : Set (MulAut V)) := by
    have hle : A ⊔ Subgroup.zpowers x ≤
        Subgroup.normalizer ((S ⊓ coreIn G M : Subgroup (MulAut V)) : Set (MulAut V)) :=
      sup_le hAN ((Subgroup.zpowers_le).2 hxN)
    rwa [hgen] at hle
  have hR : S ⊓ coreIn G M ≤ pCoreOf 2 G :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hSyl.1) hGN (h.syl.2.1.to_le inf_le_left)
  rw [h.o2] at hR
  rw [inf_comm]
  exact le_bot_iff.1 hR

theorem exists_conj_not_mem (h : GlHyp G M S A) {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    ∃ x ∈ G, x * a * x⁻¹ ∉ M := by
  by_contra hcon
  push Not at hcon
  have haN : a ∈ coreIn G M := mem_coreIn.2 fun g hg => by
    have := hcon g⁻¹ (G.inv_mem hg)
    simpa using this
  have ha2 : a ^ 2 = 1 := h.el.2 a ha
  have hP : IsPGroup 2 (Subgroup.zpowers a) :=
    isPGroup_two_of_sq_eq_one fun g hg => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [ha2]
  have hle : Subgroup.zpowers a ≤ M := (Subgroup.zpowers_le).2 (coreIn_le haN)
  obtain ⟨m, hm, hmle⟩ := exists_conj_le_of_isSylowOf h.syl hP hle
  have h1 : m * a * m⁻¹ ∈ S := hmle ⟨a, Subgroup.mem_zpowers a, by simp [MulAut.conj_apply]⟩
  have h2 : m * a * m⁻¹ ∈ coreIn G M :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_coreIn G M (h.lt.le hm)) a).1 haN
  have h3 : m * a * m⁻¹ ∈ coreIn G M ⊓ S := ⟨h2, h1⟩
  rw [h.coreIn_inf_eq_bot] at h3
  have h4 : m * a * m⁻¹ = 1 := h3
  apply ha1
  have := congrArg (fun z => m⁻¹ * z * m) h4
  simpa [mul_assoc] using this

theorem exists_conj_not_le (h : GlHyp G M S A) :
    ∃ k ∈ G, ¬ A.map (MulAut.conj k).toMonoidHom ≤ M := by
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h.ne
  obtain ⟨x, hxG, hx⟩ := h.exists_conj_not_mem haA (fun h' => ha1 (Subtype.ext h'))
  exact ⟨x, hxG, fun hle => hx (hle ⟨a, haA, by simp [MulAut.conj_apply]⟩)⟩

end GlHyp

structure GlPair (G M S A : Subgroup (MulAut V)) (k : MulAut V) : Prop extends GlHyp G M S A where
  hk : k ∈ G
  hAk : ¬ A.map (MulAut.conj k).toMonoidHom ≤ M

theorem GlHyp.exists_glPair [Finite V] {G M S A : Subgroup (MulAut V)} (h : GlHyp G M S A) :
    ∃ k, GlPair G M S A k := by
  obtain ⟨k, hk, hAk⟩ := h.exists_conj_not_le
  exact ⟨k, ⟨h, hk, hAk⟩⟩

namespace GlPair

variable {G M S A : Subgroup (MulAut V)} {k : MulAut V} (h : GlPair G M S A k)

include h

theorem B_le_G : A.map (MulAut.conj k).toMonoidHom ≤ G := map_conj_le h.hk h.A_le_G

theorem sup_eq : A ⊔ A.map (MulAut.conj k).toMonoidHom = G := by
  obtain ⟨b, hbB, hbM⟩ := IsConcreteLE.not_le_iff_exists.1 h.hAk
  have hbG : b ∈ G := h.B_le_G hbB
  apply le_antisymm
  · exact sup_le h.A_le_G h.B_le_G
  · rw [← h.gen b hbG hbM]
    exact sup_le_sup_left ((Subgroup.zpowers_le).2 hbB) A

theorem k_not_mem : k ∉ M := fun hkM =>
  h.hAk (map_conj_le hkM h.A_le_M)

theorem fixV_inf_eq_bot :
    fixV A ⊓ fixV (A.map (MulAut.conj k).toMonoidHom) = ⊥ := by
  rw [← fixV_sup, h.sup_eq, h.fix]

theorem commV_B_le :
    commV (A.map (MulAut.conj k).toMonoidHom) ≤ fixV (A.map (MulAut.conj k).toMonoidHom) := by
  rw [B19.commV_map_conj, fixV_map_conj]
  exact Subgroup.map_mono h.quad

theorem commV_G_eq : commV G = commV A ⊔ commV (A.map (MulAut.conj k).toMonoidHom) := by
  conv_lhs => rw [← h.sup_eq]
  exact B19.commV_sup _ _

theorem commV_inf_commV :
    commV A ⊓ commV (A.map (MulAut.conj k).toMonoidHom) = ⊥ :=
  le_bot_iff.1 ((inf_le_inf h.quad h.commV_B_le).trans h.fixV_inf_eq_bot.le)

theorem card_inf_fixV_zpowers_le [Finite V] {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Nat.card (commV G ⊓ fixV (Subgroup.zpowers a) : Subgroup V) ≤ Nat.card (commV A) := by
  obtain ⟨x, hxG, hxM⟩ := h.exists_conj_not_mem ha ha1
  set g' := x * a * x⁻¹ with hg'
  have hg'G : g' ∈ G := G.mul_mem (G.mul_mem hxG (h.A_le_G ha)) (G.inv_mem hxG)
  have hgen := h.gen g' hg'G hxM
  set Y : Subgroup V := commV G ⊓ fixV (Subgroup.zpowers g') with hY
  have hYA : Y ⊓ commV A = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvX, hvg⟩, hvA⟩
    have hvA' : v ∈ fixV A := h.quad hvA
    have hvG : v ∈ fixV G := by
      rw [← hgen, fixV_sup]
      exact ⟨hvA', hvg⟩
    rw [h.fix] at hvG
    exact hvG
  have hYle : Y ⊔ commV A ≤ commV G :=
    sup_le inf_le_left (G6.commV_mono h.A_le_G)
  have hcard1 : Nat.card (Y ⊔ commV A : Subgroup V) = Nat.card Y * Nat.card (commV A) := by
    have := card_sup_of_inf_eq_bot hYA
    exact this
  have hcardX : Nat.card (commV G) = Nat.card (commV A) * Nat.card (commV A) := by
    rw [h.commV_G_eq]
    have hbot : commV A ⊓ commV (A.map (MulAut.conj k).toMonoidHom) = ⊥ := h.commV_inf_commV
    rw [card_sup_of_inf_eq_bot hbot, card_commV_map_conj k A]
  have hle1 : Nat.card Y * Nat.card (commV A) ≤ Nat.card (commV A) * Nat.card (commV A) := by
    rw [← hcard1, ← hcardX]
    exact Subgroup.card_le_of_le hYle
  have hpos : 0 < Nat.card (commV A) := Nat.card_pos
  have hY1 : Nat.card Y ≤ Nat.card (commV A) := by
    have := Nat.le_of_mul_le_mul_right hle1 hpos
    exact this
  have hmap : (commV G ⊓ fixV (Subgroup.zpowers a)).map x.toMonoidHom ≤ Y := by
    rintro _ ⟨v, ⟨hvX, hva⟩, rfl⟩
    refine ⟨apply_mem_commV_of_mem hxG hvX, Glauberman.mem_fixV_zpowers.2 ?_⟩
    have hva' : a v = v := Glauberman.mem_fixV_zpowers.1 hva
    show g' (x v) = x v
    rw [hg', MulAut.mul_apply, MulAut.mul_apply, show x⁻¹ (x v) = v by simp, hva']
  calc Nat.card (commV G ⊓ fixV (Subgroup.zpowers a) : Subgroup V)
      = Nat.card ((commV G ⊓ fixV (Subgroup.zpowers a)).map x.toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := x.toMonoidHom) x.injective).symm
    _ ≤ Nat.card Y := Subgroup.card_le_of_le hmap
    _ ≤ Nat.card (commV A) := hY1

theorem lemma_three [Finite V] :
    commV A = fixV A ∧
      commV (A.map (MulAut.conj k).toMonoidHom) = fixV (A.map (MulAut.conj k).toMonoidHom) ∧
      fixV A ⊔ fixV (A.map (MulAut.conj k).toMonoidHom) = ⊤ ∧
      Nat.card (fixV A) = Nat.card A ∧
      Nat.card (fixV (A.map (MulAut.conj k).toMonoidHom)) = Nat.card A ∧
      Nat.card V = Nat.card A ^ 2 := by
  set B := A.map (MulAut.conj k).toMonoidHom with hB
  have hV1ne : commV A ≠ ⊥ := fun h0 => h.ne (commV_eq_bot_iff.1 h0)
  have hcardB : Nat.card (commV B) = Nat.card (commV A) := card_commV_map_conj k A
  have hV1pos : 1 < Nat.card (commV A) := by
    have h1 : Nat.card (commV A) ≠ 1 := fun h0 => hV1ne (Subgroup.eq_bot_of_card_eq _ h0)
    have : 0 < Nat.card (commV A) := Nat.card_pos
    omega
  have hV2ne : commV B ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hcardB
    omega
  have hAcard : Nat.card A ≤ Nat.card (commV A) := by
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV2ne
    have hyX : (y : V) ∈ commV G := by
      rw [h.commV_G_eq]
      exact Subgroup.mem_sup_right y.2
    have hyF₂ : (y : V) ∈ fixV B := h.commV_B_le y.2
    have hy_notF₁ : (y : V) ∉ fixV A := by
      intro hF1
      have : (y : V) ∈ fixV A ⊓ fixV B := ⟨hF1, hyF₂⟩
      rw [h.fixV_inf_eq_bot] at this
      exact hy1 (Subtype.ext this)
    let f : A → commV A := fun a => ⟨(a : MulAut V) y * (y : V)⁻¹, G6.mem_commV_of_mem a.2 y⟩
    have hf : Function.Injective f := by
      intro a a' haa'
      have h1 : (a : MulAut V) y * (y : V)⁻¹ = (a' : MulAut V) y * (y : V)⁻¹ :=
        congrArg Subtype.val haa'
      have h2 : (a : MulAut V) y = (a' : MulAut V) y := mul_right_cancel h1
      by_contra hne
      have hcA : (a' : MulAut V)⁻¹ * (a : MulAut V) ∈ A := A.mul_mem (A.inv_mem a'.2) a.2
      have hc1 : (a' : MulAut V)⁻¹ * (a : MulAut V) ≠ 1 := fun h0 =>
        hne (Subtype.ext (inv_mul_eq_one.1 h0).symm)
      have hcy : ((a' : MulAut V)⁻¹ * (a : MulAut V)) y = y := by
        rw [MulAut.mul_apply, h2]
        simp
      set Z : Subgroup V := commV G ⊓ fixV (Subgroup.zpowers ((a' : MulAut V)⁻¹ * (a : MulAut V)))
        with hZ
      have hle : commV A ≤ Z := by
        intro v hv
        refine ⟨G6.commV_mono h.A_le_G hv, Glauberman.mem_fixV_zpowers.2 ?_⟩
        exact h.quad hv _ hcA
      have hcardZ : Nat.card Z ≤ Nat.card (commV A) := h.card_inf_fixV_zpowers_le hcA hc1
      have heq : commV A = Z := Subgroup.eq_of_le_of_card_ge hle hcardZ
      have hyZ : (y : V) ∈ Z := ⟨hyX, Glauberman.mem_fixV_zpowers.2 hcy⟩
      rw [← heq] at hyZ
      exact hy_notF₁ (h.quad hyZ)
    exact Nat.card_le_card_of_injective f hf
  have hF1V2 : fixV A ⊓ commV B = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ h.commV_B_le).trans h.fixV_inf_eq_bot.le)
  have hc1 : Nat.card (fixV A ⊔ commV B : Subgroup V) = Nat.card (fixV A) * Nat.card (commV B) :=
    card_sup_of_inf_eq_bot hF1V2
  have hle1 : Nat.card (fixV A) * Nat.card (commV B) ≤ Nat.card V := by
    rw [← hc1]
    exact Subgroup.card_le_card_group _
  have hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := h.off
  have hF1pos : 0 < Nat.card (fixV A) := Nat.card_pos
  have hV2le : Nat.card (commV B) ≤ Nat.card A := by
    have : Nat.card (fixV A) * Nat.card (commV B) ≤ Nat.card (fixV A) * Nat.card A := by
      calc Nat.card (fixV A) * Nat.card (commV B) ≤ Nat.card V := hle1
        _ ≤ Nat.card A * Nat.card (fixV A) := hoff
        _ = Nat.card (fixV A) * Nat.card A := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left this hF1pos
  have hV2eq : Nat.card (commV B) = Nat.card A := by omega
  have hV1eq : Nat.card (commV A) = Nat.card A := by omega
  have hVeq : Nat.card V = Nat.card (fixV A) * Nat.card (commV B) := by
    apply le_antisymm
    · calc Nat.card V ≤ Nat.card A * Nat.card (fixV A) := hoff
        _ = Nat.card (fixV A) * Nat.card (commV B) := by rw [hV2eq, mul_comm]
    · exact hle1
  have htop : fixV A ⊔ commV B = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hc1, hVeq]
  have hFB : fixV B = commV B := by
    have h1 := sup_inf_eq_left_of_le (U₁ := commV B) (U₂ := fixV A) (F₁ := fixV B) (F₂ := fixV A)
      h.commV_B_le le_rfl (by rw [inf_comm]; exact h.fixV_inf_eq_bot)
    rw [sup_comm, htop, top_inf_eq] at h1
    exact h1
  have hcardFB : Nat.card (fixV B) = Nat.card (fixV A) := by
    rw [fixV_map_conj]
    exact Subgroup.card_map_of_injective (f := k.toMonoidHom) k.injective
  have hF1A : Nat.card (fixV A) = Nat.card A := by
    rw [← hcardFB, hFB, hV2eq]
  have hFA : commV A = fixV A :=
    Subgroup.eq_of_le_of_card_ge h.quad (by rw [hF1A, hV1eq])
  refine ⟨hFA, hFB.symm, ?_, hF1A, by rw [hcardFB, hF1A], ?_⟩
  · rw [← hFB] at htop
    exact htop
  · rw [hVeq, hV2eq, hF1A, pow_two]

theorem commV_G_eq_top [Finite V] : commV G = ⊤ := by
  obtain ⟨h1, h2, h3, -⟩ := h.lemma_three
  rw [h.commV_G_eq, h1, h2]
  exact h3

theorem fixV_zpowers_eq [Finite V] {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) :
    fixV (Subgroup.zpowers a) = fixV A := by
  have hle : fixV A ≤ fixV (Subgroup.zpowers a) := fun v hv x hx =>
    hv x (Subgroup.zpowers_le.2 ha hx)
  have hcard := h.card_inf_fixV_zpowers_le ha ha1
  rw [h.commV_G_eq_top, top_inf_eq, h.lemma_three.1] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end GlPair

end CFSG.CGT.PushingUpLit.BHS
