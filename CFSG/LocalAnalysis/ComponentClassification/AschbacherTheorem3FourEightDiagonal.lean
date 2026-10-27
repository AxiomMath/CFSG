module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTransfer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixGoldOne
public import CFSG.Walter.AStar.CenterOdd
public import CFSG.Walter.AStar.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]
variable {G T S Q H : Subgroup X} {g y : X}

omit [Finite X] in
theorem isQuasisimple_gw {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.GorensteinWalter.IsQuasisimple Q := by
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  exact ⟨(QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial, h.1, h.2⟩

omit [Finite X] in
theorem isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

omit [Finite X] in
theorem commutator_eq_self_of_isQuasisimple {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple K) :
    ⁅K, K⁆ = K := by
  have h1 := congrArg (Subgroup.map K.subtype) hq.1
  rwa [commutator_def, Subgroup.map_commutator, map_subtype_top] at h1

omit [Finite X] in
theorem ne_bot_of_isQuasisimple {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple K) : K ≠ ⊥ := by
  have : Nontrivial K := (isQuasisimple_gw hq).1
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  apply hab
  have ha : (a : X) ∈ (⊥ : Subgroup X) := h ▸ a.2
  have hb : (b : X) ∈ (⊥ : Subgroup X) := h ▸ b.2
  rw [Subgroup.mem_bot] at ha hb
  exact Subtype.ext (ha.trans hb.symm)

omit [Finite X] in
theorem central_or_eq_of_normal {K N : Subgroup X} (hq : CFSG.Open.IsQuasisimple K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set X)) :
    (∀ n ∈ N, ∀ k ∈ K, n * k = k * n) ∨ N = K := by
  have hn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  rcases CFSG.GorensteinWalter.normal_subgroup_le_center_or_eq_top (isQuasisimple_gw hq) _ hn
    with h | h
  · left
    intro n hn' k hk
    have h1 := Subgroup.mem_center_iff.mp (h (Subgroup.mem_subgroupOf.mpr hn' :
      (⟨n, hNK hn'⟩ : K) ∈ N.subgroupOf K)) ⟨k, hk⟩
    exact (congrArg Subtype.val h1).symm
  · right
    apply le_antisymm hNK
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ N.subgroupOf K := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

omit [Finite X] in
theorem eq_of_le_of_isQuasisimple {A B : Subgroup X} (hA : CFSG.Open.IsQuasisimple A)
    (hB : CFSG.Open.IsQuasisimple B) (hAB : A ≤ B) (hBA : B ≤ Subgroup.normalizer (A : Set X)) :
    A = B := by
  rcases central_or_eq_of_normal hB hAB hBA with h | h
  · exfalso
    apply ne_bot_of_isQuasisimple hA
    rw [← commutator_eq_self_of_isQuasisimple hA, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h b hb a (hAB ha)
  · exact h

omit [Finite X] in
theorem commutator_eq_bot_of_ne {G K K' : Subgroup X} (hK : K ≤ G) (hK' : K' ≤ G)
    (hGK : G ≤ Subgroup.normalizer (K : Set X)) (hGK' : G ≤ Subgroup.normalizer (K' : Set X))
    (hq : CFSG.Open.IsQuasisimple K) (hq' : CFSG.Open.IsQuasisimple K') (hne : K ≠ K') :
    ⁅K, K'⁆ = ⊥ := by
  have hle : ⁅K, K'⁆ ≤ K ⊓ K' := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hGK' (hK ha)) b).mp hb
      have h2 := (Subgroup.mem_normalizer_iff.mp (hGK (hK' hb)) a⁻¹).mp (K.inv_mem ha)
      have h3 := K.mul_mem ha h2
      simpa [mul_assoc] using h3
    · have h1 := (Subgroup.mem_normalizer_iff.mp (hGK' (hK ha)) b).mp hb
      exact K'.mul_mem h1 (K'.inv_mem hb)
  have hcen : ∀ n ∈ K ⊓ K', ∀ k ∈ K, n * k = k * n := by
    have hN : K ≤ Subgroup.normalizer ((K ⊓ K' : Subgroup X) : Set X) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hGK' (hK hx)⟩
    rcases central_or_eq_of_normal hq inf_le_left hN with h | h
    · exact h
    · exfalso
      have hKK' : K ≤ K' := h ▸ inf_le_right
      exact hne (eq_of_le_of_isQuasisimple hq hq' hKK' (fun x hx => hGK (hK' hx)))
  have h1 : ⁅⁅K, K'⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (hcen x (hle hx) k hk).symm
  have h2 : ⁅⁅K', K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm K' K]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [commutator_eq_self_of_isQuasisimple hq] at h3

namespace ElemCtx

theorem false_of_moved_component (c : ElemCtx G T S Q H g y) (hin : Theorem48Inputs)
    {K : Subgroup X} (hKG : K ≤ G) (hGK : G ≤ Subgroup.normalizer (K : Set X))
    (hq : CFSG.Open.IsQuasisimple K) {t : X} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set X)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e := c.elem
  have hF := c.frame
  have ht2 : t ^ 2 = 1 := e.sq_T t ht
  have htinv : t⁻¹ = t := Elem47.inv_eq_of_sq ht2
  have ht1 : t ≠ 1 := fun h => htK (h ▸ Subgroup.one_mem _)
  have htG := hF.le_normalizer ht
  have htS := c.sylowFrame.le ht
  set K' := rightConjugate K t with hK'def
  have hconj : ∀ x ∈ K, t⁻¹ * x * t ∈ K' := fun x hx => by
    rw [hK'def, mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  have hK'G : K' ≤ G := by
    intro x hx
    rw [hK'def, mem_rightConjugate_iff] at hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htG) _).mp (hKG hx)
    simpa [mul_assoc] using this
  have hGK' : G ≤ Subgroup.normalizer (K' : Set X) := by
    intro h hh
    rw [← rightConjugate_eq_self_iff, hK'def, rightConjugate_mul]
    have h1 : t * h = (t * h * t⁻¹) * t := by group
    have h2 : t * h * t⁻¹ ∈ G := (Subgroup.mem_normalizer_iff.mp htG h).mp hh
    rw [h1, ← rightConjugate_mul, (rightConjugate_eq_self_iff K _).mpr (hGK h2)]
  have hne : K ≠ K' := fun h => htK ((rightConjugate_eq_self_iff K t).mp h.symm)
  have hq' : CFSG.Open.IsQuasisimple K' :=
    isQuasisimple_of_equiv (K.equivMapOfInjective _ (MulAut.conj t⁻¹).injective) hq
  have hcomm := commutator_eq_bot_of_ne hKG hK'G hGK hGK' hq hq' hne
  have hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
    intro a ha b hb
    have h1 := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  set ZK := (Subgroup.center K).map K.subtype with hZKdef
  have hmemZK : ∀ x ∈ K, (∀ k ∈ K, k * x = x * k) → x ∈ ZK := by
    intro x hx hc
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hc k k.2), rfl⟩
  have hZKK : ZK ≤ K := Subgroup.map_subtype_le _
  have hZKc : ∀ z ∈ ZK, ∀ k ∈ K, k * z = z * k := by
    rintro _ ⟨z, hz, rfl⟩ k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  have hcap : ∀ x ∈ K, x ∈ K' → x ∈ ZK := fun x hx hx' =>
    hmemZK x hx fun k hk => hKK' k hk x hx'
  have hZK2 : IsPGroup 2 ZK := by
    refine isPGroup_of_abelian (hZKK.trans hKG) ?_ ?_ c.oddCore_eq_bot
    · exact fun x hx => mem_normalizer_map_of_characteristic (Subgroup.center K) (hGK hx)
    · exact ⟨⟨fun a b => Subtype.ext (hZKc (b : X) b.2 (a : X) (hZKK a.2))⟩⟩
  have hZKG : G ≤ Subgroup.normalizer (ZK : Set X) := fun x hx =>
    mem_normalizer_map_of_characteristic (Subgroup.center K) (hGK hx)
  have hPK : IsSylowOf 2 ((S ⊓ G) ⊓ K) K := c.isSylowOf_P.inf_of_le_normalizer hKG hGK
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have htP : ∀ x ∈ S ⊓ G, t⁻¹ * x * t ∈ S ⊓ G := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have := S.mul_mem (S.mul_mem (S.inv_mem htS) hx.1) htS
      simpa [mul_assoc] using this
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htG) x).mp hx.2
      simpa using this
  have hZt : ∀ z ∈ (T ⊔ rightConjugate T g) ⊓ G, t⁻¹ * z * t = z := by
    intro z hz
    have h1 := M_comm' e (Subgroup.mem_sup_left ht) hz.1
    calc t⁻¹ * z * t = t⁻¹ * (z * t) := by group
      _ = t⁻¹ * (t * z) := by rw [← h1]
      _ = z := by group
  have hdiag : ∀ x ∈ (S ⊓ G) ⊓ K, x * (t⁻¹ * x * t) ∈ (T ⊔ rightConjugate T g) ⊓ G := by
    intro x hx
    have hc := hKK' x hx.2 _ (hconj x hx.2)
    rw [← inf_centralizer_eq_Z e ht ht1]
    refine ⟨Subgroup.mul_mem _ hx.1 (htP x hx.1), ?_⟩
    show x * (t⁻¹ * x * t) ∈ Subgroup.centralizer {t}
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (t⁻¹ * x * t) * t = x * t⁻¹ * x * (t * t) := by group
      _ = x * t * x := by rw [htt, mul_one, htinv]
      _ = t * ((t⁻¹ * x * t) * x) := by group
      _ = t * (x * (t⁻¹ * x * t)) := by rw [← hc]
  have hsq' : ∀ x ∈ (S ⊓ G) ⊓ K, x ^ 2 = (t⁻¹ * x ^ 2 * t)⁻¹ := by
    intro x hx
    have h1 := sq_Z e (hdiag x hx)
    have hc := hKK' x hx.2 _ (hconj x hx.2)
    have h2 : (x * (t⁻¹ * x * t)) ^ 2 = x ^ 2 * (t⁻¹ * x ^ 2 * t) := by
      calc (x * (t⁻¹ * x * t)) ^ 2 = x * ((t⁻¹ * x * t) * x) * (t⁻¹ * x * t) := by
            rw [pow_two]; group
        _ = x * (x * (t⁻¹ * x * t)) * (t⁻¹ * x * t) := by rw [← hc]
        _ = x ^ 2 * (t⁻¹ * x ^ 2 * t) := by rw [pow_two]; group
    rw [h2] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hsq : ∀ x ∈ (S ⊓ G) ⊓ K, x ^ 2 ∈ ZK := by
    intro x hx
    refine hcap _ (K.pow_mem hx.2 2) ?_
    rw [hsq' x hx]
    exact Subgroup.inv_mem _ (hconj _ (K.pow_mem hx.2 2))
  have hinv : ∀ x ∈ (S ⊓ G) ⊓ K, x ^ 2 = 1 → x ∈ ZK := by
    intro x hx hx2
    refine hcap x hx.2 ?_
    have := hconj x hx.2
    rwa [hZt x (c.omegaOne_eq hin hx.1 hx2)] at this
  have hcomm2 : ∀ x ∈ (S ⊓ G) ⊓ K, ∀ y ∈ (S ⊓ G) ⊓ K, x⁻¹ * y⁻¹ * x * y ∈ ZK := by
    intro x hx y hy
    have h1 := M_comm' e (hdiag x hx).1 (hdiag y hy).1
    have hyx' := hKK' y hy.2 _ (hconj x hx.2)
    have hxy' := hKK' x hx.2 _ (hconj y hy.2)
    have e1 : x * y * ((t⁻¹ * x * t) * (t⁻¹ * y * t)) =
        y * x * ((t⁻¹ * y * t) * (t⁻¹ * x * t)) := by
      calc x * y * ((t⁻¹ * x * t) * (t⁻¹ * y * t))
          = x * (y * (t⁻¹ * x * t)) * (t⁻¹ * y * t) := by group
        _ = x * ((t⁻¹ * x * t) * y) * (t⁻¹ * y * t) := by rw [hyx']
        _ = (x * (t⁻¹ * x * t)) * (y * (t⁻¹ * y * t)) := by group
        _ = (y * (t⁻¹ * y * t)) * (x * (t⁻¹ * x * t)) := h1
        _ = y * ((t⁻¹ * y * t) * x) * (t⁻¹ * x * t) := by group
        _ = y * (x * (t⁻¹ * y * t)) * (t⁻¹ * x * t) := by rw [← hxy']
        _ = y * x * ((t⁻¹ * y * t) * (t⁻¹ * x * t)) := by group
    have e2 : x⁻¹ * y⁻¹ * x * y = t⁻¹ * (y * x * y⁻¹ * x⁻¹) * t := by
      calc x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y * ((t⁻¹ * x * t) * (t⁻¹ * y * t))) *
            ((t⁻¹ * x * t) * (t⁻¹ * y * t))⁻¹ := by group
        _ = (y * x)⁻¹ * (y * x * ((t⁻¹ * y * t) * (t⁻¹ * x * t))) *
            ((t⁻¹ * x * t) * (t⁻¹ * y * t))⁻¹ := by rw [e1]
        _ = t⁻¹ * (y * x * y⁻¹ * x⁻¹) * t := by group
    refine hcap _ ?_ ?_
    · exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hx.2) (K.inv_mem hy.2)) hx.2) hy.2
    · rw [e2]
      exact hconj _ (K.mul_mem (K.mul_mem (K.mul_mem hy.2 hx.2) (K.inv_mem hy.2))
        (K.inv_mem hx.2))
  have hcenter : ∀ v : K, (v : X) ∈ ZK → v ∈ Subgroup.center K := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := hv
    rwa [← Subtype.ext hwv]
  have hZ2 : Nat.card ZK ≤ 2 := by
    obtain ⟨PK, hPKeq⟩ := hPK
    have hmemPK : ∀ v : K, v ∈ (PK : Subgroup K) → (v : X) ∈ (S ⊓ G) ⊓ K := fun v hv =>
      hPKeq ▸ ⟨v, hv, rfl⟩
    have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center K)) :=
      QuotientGroup.mk'_surjective _
    have hab : IsMulCommutative ((PK.mapSurjective hπs : Sylow 2 (K ⧸ Subgroup.center K)) :
        Subgroup (K ⧸ Subgroup.center K)) := by
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha''⟩ := a.2
      obtain ⟨b', hb', hb''⟩ := b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha'', ← hb'', ← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      apply hcenter
      have h1 := hcomm2 _ (hmemPK b' hb') _ (hmemPK a' ha')
      simpa [mul_assoc] using h1
    have hcen2 : IsPGroup 2 (Subgroup.center K) :=
      hZK2.of_equiv ((Subgroup.center K).equivMapOfInjective _ K.subtype_injective).symm
    have h := (hin.walter_schur_two_part K (Subgroup.center K) hq le_rfl hcen2 _ hab).1
    rwa [hZKdef, Subgroup.card_map_of_injective K.subtype_injective]
  have hsame : ∀ a ∈ (S ⊓ G) ⊓ K, ∀ b ∈ (S ⊓ G) ⊓ K, a ∉ ZK → b ∉ ZK → a⁻¹ * b ∈ ZK := by
    intro a ha b hb haZ hbZ
    have hab2 : a ^ 2 = b ^ 2 := eq_of_card_le_two hZ2 (hsq a ha) (hsq b hb)
      (fun h => haZ (hinv a ha h)) (fun h => hbZ (hinv b hb h))
    obtain ⟨b', hb'def⟩ : ∃ b', b' = t⁻¹ * b * t := ⟨_, rfl⟩
    have hb'K' : b' ∈ K' := hb'def ▸ hconj b hb.2
    have hab' := hKK' a ha.2 b' hb'K'
    have h1 : (a * b') ^ 2 = 1 := by
      have hb2 : b' ^ 2 = t⁻¹ * b ^ 2 * t := by rw [hb'def, pow_two, pow_two]; group
      calc (a * b') ^ 2 = a * (b' * a) * b' := by rw [pow_two]; group
        _ = a * (a * b') * b' := by rw [← hab']
        _ = a ^ 2 * b' ^ 2 := by rw [pow_two, pow_two]; group
        _ = b ^ 2 * (t⁻¹ * b ^ 2 * t) := by rw [hb2, hab2]
        _ = (t⁻¹ * b ^ 2 * t)⁻¹ * (t⁻¹ * b ^ 2 * t) := by rw [← hsq' b hb]
        _ = 1 := inv_mul_cancel _
    have hab'P : a * b' ∈ S ⊓ G := Subgroup.mul_mem _ ha.1 (hb'def ▸ htP b hb.1)
    have h2 := hZt _ (c.omegaOne_eq hin hab'P h1)
    have hbb : t⁻¹ * b' * t = b := by
      rw [hb'def]
      calc t⁻¹ * (t⁻¹ * b * t) * t = (t * t)⁻¹ * b * (t * t) := by group
        _ = b := by rw [htt]; group
    have h2' : (t⁻¹ * a * t) * b = a * b' := by
      calc (t⁻¹ * a * t) * b = (t⁻¹ * a * t) * (t⁻¹ * b' * t) := by rw [hbb]
        _ = t⁻¹ * (a * b') * t := by group
        _ = a * b' := h2
    have hb'eq : b' = a⁻¹ * ((t⁻¹ * a * t) * b) := by rw [h2']; group
    have ha'b := hKK' b hb.2 (t⁻¹ * a * t) (hconj a ha.2)
    have h3 : a⁻¹ * b = b' * (t⁻¹ * a * t)⁻¹ := by
      calc a⁻¹ * b = a⁻¹ * (b * (t⁻¹ * a * t)) * (t⁻¹ * a * t)⁻¹ := by group
        _ = a⁻¹ * ((t⁻¹ * a * t) * b) * (t⁻¹ * a * t)⁻¹ := by rw [ha'b]
        _ = b' * (t⁻¹ * a * t)⁻¹ := by rw [hb'eq]
    refine hcap _ (K.mul_mem (K.inv_mem ha.2) hb.2) ?_
    rw [h3]
    exact K'.mul_mem hb'K' (K'.inv_mem (hconj a ha.2))
  have hPKab : ∀ a ∈ (S ⊓ G) ⊓ K, ∀ b ∈ (S ⊓ G) ⊓ K, a * b = b * a := by
    intro a ha b hb
    by_cases haZ : a ∈ ZK
    · exact (hZKc a haZ b hb.2).symm
    by_cases hbZ : b ∈ ZK
    · exact hZKc b hbZ a ha.2
    · have h1 := hsame a ha b hb haZ hbZ
      have hz := hZKc _ h1 a ha.2
      calc a * b = a * (a * (a⁻¹ * b)) := by group
        _ = a * ((a⁻¹ * b) * a) := by rw [hz]
        _ = b * a := by group
  have hZKbot : ∀ z ∈ ZK, z = 1 := by
    obtain ⟨PK, hPKeq⟩ := hPK
    have hab : IsMulCommutative (PK : Subgroup K) := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : ((a : K) : X) ∈ (S ⊓ G) ⊓ K := hPKeq ▸ ⟨a, a.2, rfl⟩
      have hb : ((b : K) : X) ∈ (S ⊓ G) ⊓ K := hPKeq ▸ ⟨b, b.2, rfl⟩
      exact Subtype.ext (hPKab _ ha _ hb)
    have hodd := CFSG.Walter.odd_card_center_of_perfect hq.1
      (CFSG.Walter.hasAbelianSylowTwo_of_sylow PK hab)
    have hcen2 : IsPGroup 2 (Subgroup.center K) :=
      hZK2.of_equiv ((Subgroup.center K).equivMapOfInjective _ K.subtype_injective).symm
    obtain ⟨n, hn⟩ := hcen2.exists_card_eq
    have hn0 : n = 0 := by
      rcases n with _ | n
      · rfl
      · rw [hn, pow_succ] at hodd
        exact absurd (Nat.even_mul.mpr (Or.inr even_two)) (Nat.not_even_iff_odd.mpr hodd)
    rw [hn0, pow_zero] at hn
    have hbot := Subgroup.card_eq_one.mp hn
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (⊥ : Subgroup K) := hbot ▸ hz
    rw [Subgroup.mem_bot] at hz'
    rw [hz']
    rfl
  have hPK1 : (S ⊓ G) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hZKbot x (hinv x hx (hZKbot _ (hsq x hx)))
  obtain ⟨-, -, hdvd⟩ := isSylowOf_iff.mp hPK
  rw [hPK1, Subgroup.relIndex_bot_left] at hdvd
  have hKodd : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hdvd)
  have hKle := le_map_oddCore hKG hGK hKodd
  rw [c.oddCore_eq_bot, Subgroup.map_bot] at hKle
  exact ne_bot_of_isQuasisimple hq (le_bot_iff.mp hKle)

end ElemCtx

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight
