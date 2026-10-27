module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowQECert
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S1

public section

namespace CFSG.ComponentClassification.AS81

namespace HeSylow

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.Native

section Facts

variable {H : Type} [Group H]

structure SylQE (X Q E F : Subgroup H) (z : H) : Prop where
  cardQE : Nat.card (Q ⊓ E : Subgroup H) = 16
  cardQF : Nat.card (Q ⊓ F : Subgroup H) = 16
  cent : ∀ x ∈ X, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z

end Facts

section Sound

variable {n : ℕ}

theorem card_inf_of_interCountN {es qs : List (Array ℕ)} {mE mQ k l : ℕ}
    (hE : enumCheckN n es mE = true) (hQ : enumCheckN n qs mQ = true) (hkl : mE = k + l)
    (h : interCountN n es qs k l = true) :
    Nat.card (grpN n qs ⊓ grpN n es : Subgroup (Equiv.Perm (Fin n))) = k := by
  simp only [interCountN, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hle1 : Nat.card (grpN n qs ⊓ grpN n es : Subgroup (Equiv.Perm (Fin n))) ≤ k := by
    rw [← h1]
    refine card_le_length
      (S := ((grpN n qs ⊓ grpN n es : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))))
      ?_
    rintro x ⟨hxQ, hxE⟩
    obtain ⟨t, ht, hr⟩ := (mem_grpN_iff hE).1 hxE
    exact ⟨t, List.mem_filter.2 ⟨ht, inLN_of_mem hQ hxQ hr⟩, hr⟩
  have hle2 : Nat.card ↥((grpN n es : Set (Equiv.Perm (Fin n))) \ grpN n qs) ≤ l := by
    rw [← h2]
    refine card_le_length ?_
    rintro x ⟨hxE, hxQ⟩
    obtain ⟨t, ht, hr⟩ := (mem_grpN_iff hE).1 hxE
    refine ⟨t, List.mem_filter.2 ⟨ht, ?_⟩, hr⟩
    by_contra hc
    exact hxQ (mem_of_inLN hQ (by simpa using hc) hr)
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (grpN n es : Set (Equiv.Perm (Fin n)))
    (grpN n qs) (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hsum
  have hE' : Nat.card ↥(grpN n es : Set (Equiv.Perm (Fin n))) = mE := card_grpN hE
  have hinter : Nat.card ↥((grpN n es : Set (Equiv.Perm (Fin n))) ∩ grpN n qs) =
      Nat.card (grpN n qs ⊓ grpN n es : Subgroup (Equiv.Perm (Fin n))) := by
    rw [Set.inter_comm]
    rfl
  omega

theorem eq_of_centQN {gs qs : List (Array ℕ)} {mX mQ : ℕ} {zt : Array ℕ}
    {Z : Equiv.Perm (Fin n)} (hX : enumCheckN n gs mX = true) (hQ : enumCheckN n qs mQ = true)
    (hz : Rep n zt Z) (h : centQN n gs qs zt = true) {x : Equiv.Perm (Fin n)}
    (hx : x ∈ grpN n gs) (hc : ∀ y ∈ grpN n qs, x * y = y * x) : x = 1 ∨ x = Z := by
  obtain ⟨t, ht, hb⟩ := forall_of_all hX h hx
  rw [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · exfalso
    rw [Bool.not_eq_true', ← Bool.not_eq_true] at hb
    refine hb (List.all_eq_true.2 fun a ha => ?_)
    exact (commN_iff ht (rep_of_validA (validA_of_mem hQ ha))).2 (hc _ (gen_mem_grpN ha))
  · exact (inZN_iff hz ht).1 hb

theorem mem_zpowers_of_eq {G : Type} [Group G] {x z : G} (h : x = 1 ∨ x = z) :
    x ∈ zpowers z := by
  rcases h with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

theorem heSylowQECheck_parts (h : heSylowQECheck = true) :
    interCountN 16 heSylE16 heSylQ16 16 48 = true ∧ interCountN 16 heSylF16 heSylQ16 16 48 = true ∧
    centQN 16 heSyl16 heSylQ16 heSylZ16 = true ∧
    interCountN 32 heAutE32 heAutQ32 16 48 = true ∧ interCountN 32 heAutF32 heAutQ32 16 48 = true ∧
    centQN 32 GrSLit.HeldFix.hfT0Tabs32.toList heAutQ32 heAutZ32 = true := by
  simp only [heSylowQECheck, Bool.and_eq_true, and_assoc] at h
  exact h

theorem sylQE16 :
    SylQE X16 Q16 E16 F16 z16 := by
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := sylCheck16_parts (sylCheck16_of he_sylowCheck)
  obtain ⟨h1, h2, h3, -⟩ := heSylowQECheck_parts he_sylowQECheck
  exact ⟨card_inf_of_interCountN hE hQ rfl h1, card_inf_of_interCountN hF hQ rfl h2,
    fun x hx hc => mem_zpowers_of_eq (eq_of_centQN hX hQ (rep_of_validA hvz) h3 hx hc)⟩

theorem sylQE32 :
    SylQE Y32 Q32 E32 F32 z32 := by
  obtain ⟨hX, hQ, hE, hF, -, hvz, -⟩ := heAutSylowCheck_parts he_autSylowCheck
  obtain ⟨-, -, -, h1, h2, h3⟩ := heSylowQECheck_parts he_sylowQECheck
  exact ⟨card_inf_of_interCountN hE hQ rfl h1, card_inf_of_interCountN hF hQ rfl h2,
    fun x hx hc => mem_zpowers_of_eq (eq_of_centQN hX hQ (rep_of_validA hvz) h3 hx hc)⟩

end Sound

section Map

variable {H G : Type} [Group H] [Group G] {X : Subgroup H} {f : ↥X →* G}

theorem trS_inf (hf : Function.Injective f) {K L : Subgroup H} :
    trS f (K ⊓ L) = trS f K ⊓ trS f L := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_trS.mp hy
    exact ⟨(apply_mem_trS_iff hf).mpr hx.1, (apply_mem_trS_iff hf).mpr hx.2⟩
  · rintro ⟨hy1, hy2⟩
    obtain ⟨x, hx, rfl⟩ := mem_trS.mp hy1
    exact (apply_mem_trS_iff hf).mpr ⟨hx, (apply_mem_trS_iff hf).mp hy2⟩

theorem SylQE.map {Q E F U : Subgroup H} {z : H} {k : ℕ} (hm : SylModel X Q E F U z k)
    (hq : SylQE X Q E F z) (hf : Function.Injective f) :
    SylQE f.range (trS f Q) (trS f E) (trS f F) (f ⟨z, hm.z_mem⟩) where
  cardQE := by
    rw [← trS_inf hf, card_trS hf (inf_le_left.trans hm.QX), hq.cardQE]
  cardQF := by
    rw [← trS_inf hf, card_trS hf (inf_le_left.trans hm.QX), hq.cardQF]
  cent y hy hc := by
    obtain ⟨x, rfl⟩ := hy
    have hx : (x : H) ∈ zpowers z := by
      refine hq.cent x x.2 fun w hw => ?_
      have h := hc (f ⟨w, hm.QX hw⟩) ((apply_mem_trS_iff hf).mpr hw)
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hf h)
    rw [← trS_zpowers hm.z_mem, apply_mem_trS_iff hf]
    exact hx

end Map

end HeSylow

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Blueprint.NativeSporadic HeSylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylModelQE_of_equiv {H : Type} [Group H] {X Q E F U : Subgroup H} {z : H} {k : ℕ}
    (hm : SylModel X Q E F U z k) (hq : SylQE X Q E F z) {S₁ : Subgroup G} (θ : ↥X ≃* ↥S₁) :
    ∃ (Q' E' F' U' : Subgroup G) (z' : G), SylModel S₁ Q' E' F' U' z' k ∧
      SylQE S₁ Q' E' F' z' := by
  let f : ↥X →* G := S₁.subtype.comp θ.toMonoidHom
  have hf : Function.Injective f := S₁.subtype_injective.comp θ.injective
  have hr : f.range = S₁ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ x).2
    · intro hy
      exact ⟨θ.symm ⟨y, hy⟩, by simp [f]⟩
  have h := hm.map f hf
  have h' := hq.map hm hf
  rw [hr] at h h'
  exact ⟨_, _, _, _, _, h, h'⟩

theorem exists_sylModelQE_of_step44
    (h44 : Step44ii) {A R : Subgroup G} {g : G} {E F S₁ : Subgroup G}
    (hset : Sec4Setting G A R g E F)
    (hSN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))) :
    ∃ (Q E' F' U : Subgroup G) (z : G) (k : ℕ), SylModel S₁ Q E' F' U z k ∧
      SylQE S₁ Q E' F' z := by
  rcases h44 G A R g E F hset S₁ hSN with ⟨_hc, P, ⟨e⟩⟩ |
    ⟨_hc, H, _, _, K, hKn, hK, hi, hC, P, ⟨e⟩⟩
  · obtain ⟨e0⟩ := nonempty_sylow_he_equiv P
    obtain ⟨Q, E', F', U, z, hm, hq⟩ :=
      exists_sylModelQE_of_equiv sylModel16 sylQE16 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 4, hm, hq⟩
  · obtain ⟨e0⟩ := nonempty_sylow_aut_equiv hKn hK hi hC P
    obtain ⟨Q, E', F', U, z, hm, hq⟩ :=
      exists_sylModelQE_of_equiv sylModel32 sylQE32 (e.trans e0).symm
    exact ⟨Q, E', F', U, z, 8, hm, hq⟩

theorem sec4Q_qe
    (h44 : Step44ii) {A R : Subgroup G} {g : G}
    {E F S₁ Q : Subgroup G} {z : G} (hQ : Sec4Q G A R g E F S₁ Q z) :
    Nat.card (Q ⊓ E : Subgroup G) = 16 ∧ Nat.card (Q ⊓ F : Subgroup G) = 16 ∧
      (∀ x ∈ S₁, (∀ y ∈ Q, x * y = y * x) → x ∈ zpowers z) ∧
      ∀ Q' : Subgroup G, Q' ≤ S₁ → Nat.card Q' = 2 ^ 7 → (∀ x ∈ Q', x ^ 2 ∈ zpowers z) →
        (∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers z) → Q' = Q := by
  obtain ⟨Q', E', F', U, z', k, hm, hq⟩ := exists_sylModelQE_of_step44 h44 hQ.setting hQ.sylowN
  have hzz : zpowers z' = zpowers z := by rw [← hm.center_X, hQ.center_S₁]
  have hQQ : Q' = Q := hQ.unique Q' hm.QX hm.extraspecial hm.cardQ (by
    rw [hm.center_Q, hm.center_X])
  subst hQQ
  have hEF := sup_le_of_isSylowOf_normalizer hQ.setting hQ.sylowN
  have hcard : ∀ V : Subgroup G, V ≤ S₁ → IsElemAbelian 2 V → Nat.card V = 64 →
      Nat.card (Q' ⊓ V : Subgroup G) = 16 := by
    intro V hV hVe hc
    rcases hm.uniqE V hV hVe (by rw [hc]; norm_num) with rfl | rfl
    · exact hq.cardQE
    · exact hq.cardQF
  refine ⟨hcard E (le_sup_left.trans hEF) hQ.setting.frame.elemE hQ.setting.frame.cardE,
    hcard F (le_sup_right.trans hEF) hQ.setting.frame.elemF hQ.setting.frame.cardF,
    fun x hx hc => ?_, fun Q'' hle hc hsq hcomm => ?_⟩
  · rw [← hzz]
    exact hq.cent x hx hc
  · rw [← hzz] at hsq hcomm
    exact hm.unique Q'' hle hc hsq hcomm

end CFSG.ComponentClassification.AS81
