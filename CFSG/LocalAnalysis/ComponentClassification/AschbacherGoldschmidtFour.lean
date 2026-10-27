module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.GoldschmidtFour

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Open
open scoped Pointwise commutatorElement

variable {Y : Type*} [Group Y]

theorem conj_mem_rightConjugate {Q : Subgroup Y} {x : Y} (hx : x ∈ Q) (g : Y) :
    g⁻¹ * x * g ∈ rightConjugate Q g := by
  rw [mem_rightConjugate_iff]
  simpa [mul_assoc] using hx

theorem rightConjugate_mono {Q R : Subgroup Y} (h : Q ≤ R) (g : Y) :
    rightConjugate Q g ≤ rightConjugate R g :=
  Subgroup.map_mono h

theorem rightConjugate_inf (Q R : Subgroup Y) (g : Y) :
    rightConjugate (Q ⊓ R) g = rightConjugate Q g ⊓ rightConjugate R g :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem rightConjugate_inv_rightConjugate (Q : Subgroup Y) (g : Y) :
    rightConjugate (rightConjugate Q g⁻¹) g = Q := by
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

theorem rightConjugate_rightConjugate_inv (Q : Subgroup Y) (g : Y) :
    rightConjugate (rightConjugate Q g) g⁻¹ = Q := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem rightConjugate_of_mem_normalizer {Q : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (Q : Set Y)) : rightConjugate Q g = Q :=
  (rightConjugate_eq_self_iff Q g).2 hg

theorem isPGroup_rightConjugate {p : ℕ} {Q : Subgroup Y} (hQ : IsPGroup p Q) (g : Y) :
    IsPGroup p (rightConjugate Q g) :=
  hQ.map _

theorem mem_normalizer_of_conj_mem [Finite Y] {Q : Subgroup Y} {g : Y}
    (h : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : g ∈ Subgroup.normalizer (Q : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem rightConjugate_le_normalizer {A Q : Subgroup Y}
    (h : A ≤ Subgroup.normalizer (Q : Set Y)) (g : Y) :
    rightConjugate A g ≤ Subgroup.normalizer (rightConjugate Q g : Set Y) := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  rw [← rightConjugate_eq_self_iff, rightConjugate_mul]
  have hx' : g * x = g * x * g⁻¹ * g := by group
  rw [hx', ← rightConjugate_mul, rightConjugate_of_mem_normalizer (h hx)]

theorem mem_smul_sylow_iff {p : ℕ} (Q : Sylow p Y) (d x : Y) :
    x ∈ ((d • Q : Sylow p Y) : Subgroup Y) ↔ d⁻¹ * x * d ∈ (Q : Subgroup Y) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem exists_conj_le_of_isPGroup [Finite Y] {K A B : Subgroup Y} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (hAK : A ≤ K) (hBK : B ≤ K) :
    ∃ a ∈ K, ∃ R : Subgroup Y, IsPGroup 2 R ∧ B ≤ R ∧ rightConjugate A a ≤ R := by
  obtain ⟨RA, hRA⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨RB, hRB⟩ := (hB.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K RA RB
  refine ⟨(c : Y)⁻¹, K.inv_mem c.2, (RB : Subgroup K).map K.subtype, RB.isPGroup'.map _, ?_, ?_⟩
  · intro b hb
    exact ⟨⟨b, hBK hb⟩, hRB hb, rfl⟩
  · intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have hxK : x ∈ K := by
      have : x = (c : Y) * ((c : Y)⁻¹ * x * c) * (c : Y)⁻¹ := by group
      rw [this]
      exact K.mul_mem (K.mul_mem c.2 (hAK hx)) (K.inv_mem c.2)
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, ← hc, mem_smul_sylow_iff]
    exact hRA (show ((c⁻¹ * ⟨x, hxK⟩ * c : K) : Y) ∈ A from hx)

theorem comm_of_mem {V : Subgroup Y} (hV : IsMulCommutative V) {a b : Y} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val (hV.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem inv_eq_of_sq {a : Y} (ha : a ^ 2 = 1) : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one, ← sq, ha]

structure Hyp (S : Sylow 2 Y) (V : Subgroup Y) : Prop where
  le : V ≤ S
  elem : IsElemAbelian 2 V
  weak : ∀ h : Y, rightConjugate V h ≤ S → rightConjugate V h = V

namespace Hyp

variable {S : Sylow 2 Y} {V : Subgroup Y}

theorem isPGroup (hV : Hyp S V) : IsPGroup 2 V := S.isPGroup'.to_le hV.le

theorem comm (hV : Hyp S V) {a b : Y} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  comm_of_mem hV.elem.1 ha hb

theorem sq_eq_one (hV : Hyp S V) {a : Y} (ha : a ∈ V) : a ^ 2 = 1 := hV.elem.2 a ha

theorem le_normalizer (hV : Hyp S V) : (S : Subgroup Y) ≤ Subgroup.normalizer (V : Set Y) := by
  intro x hx
  rw [← rightConjugate_eq_self_iff]
  apply hV.weak
  intro y hy
  rw [mem_rightConjugate_iff] at hy
  have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
  rw [this]
  exact S.mul_mem (S.mul_mem (S.inv_mem hx) (hV.le hy)) hx

theorem le_normalizer_of_isPGroup [Finite Y] (hV : Hyp S V) {R : Subgroup Y}
    (hR : IsPGroup 2 R) {c : Y} (hcR : rightConjugate V c ≤ R) :
    R ≤ Subgroup.normalizer (rightConjugate V c : Set Y) := by
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq Y Q S
  have hmem : ∀ y, y ∈ (S : Subgroup Y) ↔ d⁻¹ * y * d ∈ (Q : Subgroup Y) := fun y => by
    rw [← hd, mem_smul_sylow_iff]
  have hc : rightConjugate V (c * d⁻¹) = V := by
    apply hV.weak
    intro y hy
    rw [← rightConjugate_mul, mem_rightConjugate_iff, inv_inv] at hy
    rw [hmem]
    exact hRQ (hcR hy)
  have hVc : rightConjugate V c = rightConjugate V d := by
    conv_lhs => rw [show c = c * d⁻¹ * d by group, ← rightConjugate_mul, hc]
  intro r hr
  rw [hVc]
  have hdr : d * r * d⁻¹ ∈ (S : Subgroup Y) := by
    rw [hmem]
    simpa [mul_assoc] using hRQ hr
  exact rightConjugate_le_normalizer le_rfl d
    ((mem_rightConjugate_iff _ _ _).2 (hV.le_normalizer hdr))

end Hyp

section CommHom

variable {V : Subgroup Y} {t : Y}

@[expose] def commHom (hV : IsMulCommutative V) (ht : t ∈ Subgroup.normalizer (V : Set Y)) :
    V →* Y where
  toFun e := ⁅(e : Y), t⁆
  map_one' := by simp
  map_mul' a b := by
    have hx : t * (a : Y)⁻¹ * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 ht _).1 (V.inv_mem a.2)
    have hy : t * (b : Y)⁻¹ * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 ht _).1 (V.inv_mem b.2)
    have h1 := comm_of_mem hV hx hy
    have h2 := comm_of_mem hV b.2 hx
    show ⁅((a * b : V) : Y), t⁆ = ⁅(a : Y), t⁆ * ⁅(b : Y), t⁆
    rw [Subgroup.coe_mul, commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc (a : Y) * b * t * ((a : Y) * b)⁻¹ * t⁻¹
        = a * (b * ((t * (b : Y)⁻¹ * t⁻¹) * (t * (a : Y)⁻¹ * t⁻¹))) := by group
      _ = a * ((b * (t * (a : Y)⁻¹ * t⁻¹)) * (t * (b : Y)⁻¹ * t⁻¹)) := by
          rw [← h1]; simp only [mul_assoc]
      _ = a * (((t * (a : Y)⁻¹ * t⁻¹) * b) * (t * (b : Y)⁻¹ * t⁻¹)) := by rw [h2]
      _ = a * t * (a : Y)⁻¹ * t⁻¹ * (b * t * (b : Y)⁻¹ * t⁻¹) := by group

theorem commHom_apply (hV : IsMulCommutative V) (ht : t ∈ Subgroup.normalizer (V : Set Y))
    (e : V) : commHom hV ht e = ⁅(e : Y), t⁆ := rfl

theorem commHom_mem (hV : IsMulCommutative V) (ht : t ∈ Subgroup.normalizer (V : Set Y))
    (e : V) : commHom hV ht e ∈ V := by
  rw [commHom_apply, commutatorElement_def]
  have h : t * (e : Y)⁻¹ * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 ht _).1 (V.inv_mem e.2)
  simpa [mul_assoc] using V.mul_mem e.2 h

theorem mem_ker_commHom (hV : IsMulCommutative V) (ht : t ∈ Subgroup.normalizer (V : Set Y))
    (e : V) : e ∈ (commHom hV ht).ker ↔ (e : Y) * t = t * e := by
  rw [MonoidHom.mem_ker, commHom_apply, commutatorElement_eq_one_iff_mul_comm]

theorem commHom_mul_comm (hV : IsMulCommutative V) (ht : t ∈ Subgroup.normalizer (V : Set Y))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (ht2 : t ^ 2 = 1) (e : V) :
    commHom hV ht e * t = t * commHom hV ht e := by
  obtain ⟨e, he⟩ := e
  have ht' : t⁻¹ = t := inv_eq_of_sq ht2
  have he' : e⁻¹ = e := inv_eq_of_sq (hV2 e he)
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hx : t * e * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 ht _).1 he
  have hc := comm_of_mem hV he hx
  rw [ht'] at hc
  rw [commHom_apply, commutatorElement_def]
  simp only [he', ht']
  calc e * t * e * t * t = e * t * e := by simp only [mul_assoc, htt, mul_one]
    _ = e * (t * e * t) * t := by simp only [mul_assoc, htt, mul_one]
    _ = (t * e * t) * e * t := by rw [hc]
    _ = t * (e * t * e * t) := by simp only [mul_assoc]

theorem commutator_zpowers_le_range (hV : IsMulCommutative V)
    (ht : t ∈ Subgroup.normalizer (V : Set Y)) (ht2 : t ^ 2 = 1) :
    ⁅V, Subgroup.zpowers t⁆ ≤ (commHom hV ht).range := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ht2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [hk, h, zpow_add, zpow_mul, h2]
    simp
  · rw [hk, h, zpow_add, zpow_mul, h2]
    simp only [one_zpow, zpow_one, one_mul]
    exact ⟨⟨g₁, hg₁⟩, rfl⟩

end CommHom

theorem card_range_mul_card_le [Finite Y] {G : Type*} [Group G] [Finite G] (ψ : G →* Y)
    {A C : Subgroup Y} (hAC : A ≤ C) (hRC : ψ.range ≤ C) (hC : Nat.card C ≤ Nat.card ψ.ker) :
    Nat.card ψ.range * Nat.card A ≤ Nat.card (A.comap ψ) := by
  have h1 : Nat.card (A.comap ψ) * A.relIndex ψ.range = Nat.card G := by
    rw [← Subgroup.index_comap]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card G := Subgroup.card_ker_mul_card_range ψ
  have h4 : A.relIndex C * Nat.card A = Nat.card C := by
    have := Subgroup.relIndex_mul_card (H := A) (K := C)
    rwa [inf_of_le_left hAC] at this
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hne : A.relIndex C ≠ 0 := by
    intro h
    rw [h, zero_mul] at h4
    omega
  have h3 : A.relIndex ψ.range ≤ A.relIndex C := Subgroup.relIndex_le_of_le_right hRC hne
  have hr : 0 < A.relIndex ψ.range := by
    rcases Nat.eq_zero_or_pos (A.relIndex ψ.range) with h | h
    · rw [h, mul_zero] at h1; omega
    · exact h
  have key : A.relIndex ψ.range * (Nat.card ψ.range * Nat.card A) ≤
      A.relIndex ψ.range * Nat.card (A.comap ψ) := by
    calc A.relIndex ψ.range * (Nat.card ψ.range * Nat.card A)
        ≤ A.relIndex C * (Nat.card ψ.range * Nat.card A) := Nat.mul_le_mul_right _ h3
      _ = Nat.card C * Nat.card ψ.range := by rw [← h4]; ring
      _ ≤ Nat.card ψ.ker * Nat.card ψ.range := Nat.mul_le_mul_right _ hC
      _ = A.relIndex ψ.range * Nat.card (A.comap ψ) := by rw [h2, ← h1, mul_comm]
  exact Nat.le_of_mul_le_mul_left key hr

theorem exists_card_commutator_le [Finite Y] {S : Sylow 2 Y} {V : Subgroup Y} (hV : Hyp S V)
    {t : Y} (htS : t ∈ (S : Subgroup Y)) (htV : ∃ k : Y, t ∈ rightConjugate V k) :
    ∃ U ≤ V, ∃ h : Y, rightConjugate U h ≤ S ∧
      Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) ≤ V.relIndex (rightConjugate U h) := by
  have : Nonempty {k : Y // t ∈ rightConjugate V k} := by
    obtain ⟨k, hk⟩ := htV
    exact ⟨⟨k, hk⟩⟩
  obtain ⟨⟨k, hk⟩, hmax⟩ := Finite.exists_max
    (fun k : {k : Y // t ∈ rightConjugate V k} =>
      Nat.card (V ⊓ rightConjugate V k.1 : Subgroup Y))
  set V' := rightConjugate V k with hV'def
  set V0 := V ⊓ V'
  set V1 := V0 ⊔ Subgroup.zpowers t
  have ht2 : t ^ 2 = 1 := by
    have h := hV.sq_eq_one ((mem_rightConjugate_iff _ _ _).1 hk)
    rw [conj_pow] at h
    have : t ^ 2 = k⁻¹ * (k * t ^ 2 * k⁻¹) * k := by group
    rw [this, h]
    group
  have htN : t ∈ Subgroup.normalizer (V : Set Y) := hV.le_normalizer htS
  have hV'comm : ∀ {a b : Y}, a ∈ V' → b ∈ V' → a * b = b * a := by
    intro a b ha hb
    rw [hV'def, mem_rightConjugate_iff] at ha hb
    have h := hV.comm ha hb
    have h' : k * (a * b) * k⁻¹ = k * (b * a) * k⁻¹ := by
      calc k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
        _ = (k * b * k⁻¹) * (k * a * k⁻¹) := h
        _ = k * (b * a) * k⁻¹ := by group
    simpa using h'
  set ψ := commHom hV.elem.1 htN
  set V2 := (V0.comap ψ).map V.subtype
  have hV2V : V2 ≤ V := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hV2mem : ∀ {e : Y}, e ∈ V2 → ⁅e, t⁆ ∈ V0 := by
    rintro _ ⟨e, he, rfl⟩
    exact he
  have hV0V : V0 ≤ V := inf_le_left
  have hV0V' : V0 ≤ V' := inf_le_right
  have htV' : t ∈ V' := hk
  have hV1V' : V1 ≤ V' := sup_le hV0V' (Subgroup.zpowers_le.2 htV')
  have hV0V2 : V0 ≤ V2 := by
    intro e he
    refine ⟨⟨e, hV0V he⟩, ?_, rfl⟩
    show ⁅e, t⁆ ∈ V0
    rw [commutatorElement_eq_one_iff_mul_comm.2 (hV'comm (hV0V' he) htV')]
    exact V0.one_mem
  have hV'N1 : V' ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro x hx
    apply mem_normalizer_of_conj_mem
    intro y hy
    rw [hV'comm hx (hV1V' hy), mul_inv_cancel_right]
    exact hy
  have hV2N1 : V2 ≤ Subgroup.normalizer (V1 : Set Y) := by
    intro e he
    have heV := hV2V he
    apply mem_normalizer_of_conj_mem
    have hle : V1 ≤ V1.comap (MulAut.conj e).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro z hz
        show e * z * e⁻¹ ∈ V1
        rw [hV.comm heV (hV0V hz), mul_inv_cancel_right]
        exact Subgroup.mem_sup_left hz
      · rw [Subgroup.zpowers_le]
        show e * t * e⁻¹ ∈ V1
        have h : e * t * e⁻¹ = ⁅e, t⁆ * t := by rw [commutatorElement_def]; group
        rw [h]
        exact V1.mul_mem (Subgroup.mem_sup_left (hV2mem he))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    intro y hy
    exact hle hy
  have hV2p : IsPGroup 2 V2 := hV.isPGroup.to_le hV2V
  have hV'p : IsPGroup 2 V' := isPGroup_rightConjugate hV.isPGroup k
  obtain ⟨a, haN, R, hRp, hV'R, hV2R⟩ := exists_conj_le_of_isPGroup hV2p hV'p hV2N1 hV'N1
  have hRN : R ≤ Subgroup.normalizer (V' : Set Y) := hV.le_normalizer_of_isPGroup hRp hV'R
  have hstep : rightConjugate (rightConjugate V2 a) k⁻¹ ≤ Subgroup.normalizer (V : Set Y) := by
    have h := rightConjugate_le_normalizer (hV2R.trans hRN) k⁻¹
    rwa [hV'def, rightConjugate_rightConjugate_inv] at h
  obtain ⟨n, hnN, R', hR'p, hSR', hnR'⟩ := exists_conj_le_of_isPGroup
    (isPGroup_rightConjugate (isPGroup_rightConjugate hV2p a) k⁻¹) S.isPGroup' hstep
    hV.le_normalizer
  have hR'S : R' = S := S.is_maximal' hR'p hSR'
  rw [hR'S, rightConjugate_mul, rightConjugate_mul, ← mul_assoc] at hnR'
  set h := a * k⁻¹ * n with hhdef
  have hV1h : rightConjugate V1 h ≤ V := by
    have h1 : rightConjugate V1 h = rightConjugate (rightConjugate V1 k⁻¹) n := by
      rw [hhdef, ← rightConjugate_mul, ← rightConjugate_mul,
        rightConjugate_of_mem_normalizer haN]
    rw [h1]
    calc rightConjugate (rightConjugate V1 k⁻¹) n
        ≤ rightConjugate (rightConjugate V' k⁻¹) n :=
          rightConjugate_mono (rightConjugate_mono hV1V' _) _
      _ = V := by
          rw [hV'def, rightConjugate_rightConjugate_inv, rightConjugate_of_mem_normalizer hnN]
  have hth : t ∈ rightConjugate V h⁻¹ := by
    rw [mem_rightConjugate_iff, inv_inv]
    exact hV1h (conj_mem_rightConjugate (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) h)
  have hle : Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) ≤ Nat.card V0 := hmax ⟨h⁻¹, hth⟩
  have hcardh : Nat.card (V ⊓ rightConjugate V h : Subgroup Y) =
      Nat.card (V ⊓ rightConjugate V h⁻¹ : Subgroup Y) := by
    rw [← rightConjugate_card (V ⊓ rightConjugate V h⁻¹) h, rightConjugate_inf,
      rightConjugate_inv_rightConjugate, inf_comm]
  have hV0h : rightConjugate V0 h = V ⊓ rightConjugate V h := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact le_inf ((rightConjugate_mono le_sup_left h).trans hV1h) (rightConjugate_mono hV0V h)
    · rw [rightConjugate_card, hcardh]
      exact hle
  have hinter : V ⊓ rightConjugate V2 h = rightConjugate V0 h := by
    apply le_antisymm
    · rw [hV0h]
      exact inf_le_inf_left _ (rightConjugate_mono hV2V h)
    · exact le_inf (hV0h ▸ inf_le_left) (rightConjugate_mono hV0V2 h)
  have hrel : V.relIndex (rightConjugate V2 h) * Nat.card V0 = Nat.card V2 := by
    have h' := Subgroup.relIndex_mul_card (H := V) (K := rightConjugate V2 h)
    rwa [hinter, rightConjugate_card, rightConjugate_card] at h'
  have hcount : Nat.card ψ.range * Nat.card V0 ≤ Nat.card V2 := by
    have hcomap : Nat.card V2 = Nat.card (V0.comap ψ) :=
      Subgroup.card_map_of_injective V.subtype_injective
    rw [hcomap]
    refine card_range_mul_card_le ψ (C := ψ.ker.map V.subtype) ?_ ?_ ?_
    · intro e he
      refine ⟨⟨e, hV0V he⟩, ?_, rfl⟩
      exact (mem_ker_commHom _ _ _).2 (hV'comm (hV0V' he) htV')
    · rintro _ ⟨x, rfl⟩
      refine ⟨⟨ψ x, commHom_mem _ _ x⟩, ?_, rfl⟩
      exact (mem_ker_commHom _ _ _).2 (commHom_mul_comm _ _ hV.elem.2 ht2 x)
    · rw [Subgroup.card_map_of_injective V.subtype_injective]
  have hcomm : Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) ≤ Nat.card ψ.range :=
    Subgroup.card_le_of_le (commutator_zpowers_le_range hV.elem.1 htN ht2)
  refine ⟨V2, hV2V, h, hnR', ?_⟩
  have hpos : 0 < Nat.card V0 := Nat.card_pos
  have key : Nat.card (⁅V, Subgroup.zpowers t⁆ : Subgroup Y) * Nat.card V0 ≤
      V.relIndex (rightConjugate V2 h) * Nat.card V0 := by
    rw [hrel]
    exact (Nat.mul_le_mul_right _ hcomm).trans hcount
  exact Nat.le_of_mul_le_mul_right key hpos

theorem relIndex_ne_zero_of_finite [Finite Y] (H K : Subgroup Y) : H.relIndex K ≠ 0 := by
  intro h
  have h' := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [h, zero_mul] at h'
  exact (Nat.card_pos (α := K)).ne h'

theorem goldschmidt_theorem_four_holds : ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 2 Y)
    (V : Subgroup Y), V ≤ P → IsElemAbelian 2 V →
    (∀ h : Y, rightConjugate V h ≤ P → rightConjugate V h = V) →
    (∃ v ∈ V, ∃ h : Y, h⁻¹ * v * h ∈ (P : Subgroup Y) ∧ h⁻¹ * v * h ∉ V) →
    ∃ U ≤ V, ∃ h : Y, rightConjugate U h ≤ P ∧ ¬ rightConjugate U h ≤ V ∧
      ∀ w ∈ rightConjugate U h,
        Nat.card (⁅V, Subgroup.zpowers w⁆ : Subgroup Y) ≤ V.relIndex (rightConjugate U h) := by
  intro Y _ _ P V hVP hEA hwc hnsc
  obtain ⟨v, hv, g, hgP, hgV⟩ := hnsc
  have hV : Hyp P V := ⟨hVP, hEA, hwc⟩
  have : Nonempty {p : Subgroup Y × Y // p.1 ≤ V ∧ rightConjugate p.1 p.2 ≤ P} :=
    ⟨⟨(⊥, 1), bot_le, by rw [rightConjugate_one]; exact bot_le⟩⟩
  obtain ⟨⟨⟨U, h⟩, hUV, hUP⟩, hmax⟩ := Finite.exists_max
    (fun p : {p : Subgroup Y × Y // p.1 ≤ V ∧ rightConjugate p.1 p.2 ≤ P} =>
      V.relIndex (rightConjugate p.1.1 p.1.2))
  refine ⟨U, hUV, h, hUP, ?_, ?_⟩
  · intro hle
    have h1 : V.relIndex (rightConjugate U h) = 1 := Subgroup.relIndex_eq_one.2 hle
    have hzP : rightConjugate (Subgroup.zpowers v) g ≤ P := by
      rw [rightConjugate, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      simpa [MulAut.conj_apply] using hgP
    have h2 := hmax ⟨(Subgroup.zpowers v, g), Subgroup.zpowers_le.2 hv, hzP⟩
    have hne1 : V.relIndex (rightConjugate (Subgroup.zpowers v) g) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro hle'
      exact hgV (hle' (conj_mem_rightConjugate (Subgroup.mem_zpowers v) g))
    have hne0 := relIndex_ne_zero_of_finite V (rightConjugate (Subgroup.zpowers v) g)
    simp only at h2
    omega
  · intro w hw
    have hwV : w ∈ rightConjugate V h := rightConjugate_mono hUV h hw
    obtain ⟨U', hU'V, h', hU'P, hcard⟩ := exists_card_commutator_le hV (hUP hw) ⟨h, hwV⟩
    exact hcard.trans (hmax ⟨(U', h'), hU'V, hU'P⟩)

end CFSG.ComponentClassification.GoldschmidtFour
