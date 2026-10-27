module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.PartA
public import CFSG.ClassicalInvolution.LBalance.Glauberman.InvariantComplement
public import CFSG.ClassicalInvolution.LBalance.SylowFixing

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open SemidirectProduct CFSG.ABGLocalTools

section PartBCore

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {A : Subgroup (MulAut G)}

omit [Finite G] in
theorem inr_conj_of_mem_tSub {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} {B : Subgroup A} (a : A)
    {y : AutExt A} (hy : y ∈ tSub S A hA B) :
    (inr a : AutExt A) * y * (inr a)⁻¹ = (y * (inr y.right)⁻¹) * inr (a * y.right * a⁻¹) := by
  obtain ⟨l, b, rfl⟩ : ∃ l b, y = inl l * inr b := ⟨y.left, y.right, inl_inr_decomp y⟩
  have hl : (inl l * inr b : AutExt A).left = l := by simp [mul_left]
  have hr : (inl l * inr b : AutExt A).right = b := by simp [mul_right]
  have hlS : l ∈ S := hl ▸ hy.1
  have h1 : (inr a : AutExt A) * inl l * (inr a)⁻¹ = inl l := by
    have := inl_aut (φ := A.subtype) a l
    rw [map_inv] at this
    rw [← this]
    show inl ((a : MulAut G) l) = inl l
    rw [hA _ a.2 _ hlS]
  rw [hr]
  calc (inr a : AutExt A) * (inl l * inr b) * (inr a)⁻¹
      = ((inr a : AutExt A) * inl l * (inr a)⁻¹) *
          ((inr a : AutExt A) * inr b * (inr a)⁻¹) := by group
    _ = (inl l * inr b * (inr b)⁻¹) * inr (a * b * a⁻¹) := by
        rw [h1, map_mul, map_mul, map_inv]
        group

omit [Finite G] in
theorem inr_mem_normalizer_of_inr_le {hA : ∀ α ∈ A, ∀ s ∈ S, α s = s} {B : Subgroup A} {a : A}
    (ha : ∀ b ∈ B, a * b * a⁻¹ ∈ B) (ha' : ∀ b ∈ B, a⁻¹ * b * a ∈ B)
    {Y : Subgroup (AutExt A)} (hYT : Y ≤ tSub S A hA B)
    (hBY : ∀ b ∈ B, (inr b : AutExt A) ∈ Y) :
    (inr a : AutExt A) ∈ Subgroup.normalizer (Y : Set (AutExt A)) := by
  have key : ∀ a₀ : A, (∀ b ∈ B, a₀ * b * a₀⁻¹ ∈ B) → ∀ y ∈ Y,
      (inr a₀ : AutExt A) * y * (inr a₀)⁻¹ ∈ Y := by
    intro a₀ ha₀ y hy
    rw [inr_conj_of_mem_tSub (hA := hA) (B := B) a₀ (hYT hy)]
    exact Y.mul_mem (Y.mul_mem hy (Y.inv_mem (hBY _ (hYT hy).2))) (hBY _ (ha₀ _ (hYT hy).2))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (fun b hb => by simpa using ha' b hb) _ hy
  simpa [mul_assoc, map_inv] using this

end PartBCore

section Helpers

variable {Ω : Type*} [Group Ω]

@[expose] def omegaCenter (W : Subgroup Ω) : Subgroup Ω where
  carrier := {v | v ∈ W ∧ (∀ w ∈ W, w * v = v * w) ∧ v * v = 1}
  one_mem' := ⟨W.one_mem, fun w _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hac, ha2⟩ ⟨hb, hbc, hb2⟩
    refine ⟨W.mul_mem ha hb, fun w hw => ?_, ?_⟩
    · calc w * (a * b) = (w * a) * b := by group
        _ = (a * w) * b := by rw [hac w hw]
        _ = a * (w * b) := by group
        _ = a * (b * w) := by rw [hbc w hw]
        _ = a * b * w := by group
    · have hba : b * a = a * b := hac b hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, hac, ha2⟩
    refine ⟨W.inv_mem ha, fun w hw => ?_, ?_⟩
    · have h1 := hac w hw
      calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
        _ = a⁻¹ * (w * a) * a⁻¹ := by rw [h1]
        _ = a⁻¹ * w := by group
    · calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha2, inv_one]

theorem mem_omegaCenter {W : Subgroup Ω} {v : Ω} :
    v ∈ omegaCenter W ↔ v ∈ W ∧ (∀ w ∈ W, w * v = v * w) ∧ v * v = 1 := Iff.rfl

theorem omegaCenter_le (W : Subgroup Ω) : omegaCenter W ≤ W := fun _ hv => hv.1

theorem mem_normalizer_omegaCenter {W : Subgroup Ω} {g : Ω}
    (hg : g ∈ Subgroup.normalizer (W : Set Ω)) :
    g ∈ Subgroup.normalizer (omegaCenter W : Set Ω) := by
  have key : ∀ g' : Ω, g' ∈ Subgroup.normalizer (W : Set Ω) → ∀ v ∈ omegaCenter W,
      g' * v * g'⁻¹ ∈ omegaCenter W := by
    intro g' hg' v hv
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg' v).1 hv.1, fun w hw => ?_, ?_⟩
    · have hw' : g'⁻¹ * w * g' ∈ W := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg') w).1 hw
        simpa using this
      have h1 := hv.2.1 _ hw'
      calc w * (g' * v * g'⁻¹) = g' * ((g'⁻¹ * w * g') * v) * g'⁻¹ := by group
        _ = g' * (v * (g'⁻¹ * w * g')) * g'⁻¹ := by rw [h1]
        _ = g' * v * g'⁻¹ * w := by group
    · calc g' * v * g'⁻¹ * (g' * v * g'⁻¹) = g' * (v * v) * g'⁻¹ := by group
        _ = 1 := by rw [hv.2.2]; group
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key g hg v, fun hv => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hv
  simpa [mul_assoc] using this

theorem mem_normalizer_inf {g : Ω} {X Y : Subgroup Ω} (hX : g ∈ Subgroup.normalizer (X : Set Ω))
    (hY : g ∈ Subgroup.normalizer (Y : Set Ω)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup Ω) : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro y
  exact ⟨fun h => ⟨(hX y).1 h.1, (hY y).1 h.2⟩, fun h => ⟨(hX y).2 h.1, (hY y).2 h.2⟩⟩

theorem mem_normalizer_of_commute {r : Ω} {Y : Subgroup Ω} (h : ∀ y ∈ Y, r * y = y * r) :
    r ∈ Subgroup.normalizer (Y : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : r * y * r⁻¹ = y := by rw [h y hy]; group
    rw [this]
    exact hy
  · intro hy
    have h1 := h _ hy
    have : r⁻¹ * (r * y * r⁻¹) * r = r * y * r⁻¹ := by
      calc r⁻¹ * (r * y * r⁻¹) * r = r⁻¹ * ((r * y * r⁻¹) * r) := by group
        _ = r⁻¹ * (r * (r * y * r⁻¹)) := by rw [← h1]
        _ = r * y * r⁻¹ := by group
    have e : r⁻¹ * (r * y * r⁻¹) * r = y := by group
    rw [e] at this
    rw [this]
    exact hy

end Helpers

section Main

variable {G : Type} [Group G] [Finite G] {S : Subgroup G}

theorem partB_core
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index)
    {U : Subgroup (MulAut G)} {x : MulAut G}
    (hU : ∀ u ∈ U, ∀ s ∈ S, u s = s) (hx : ∀ s ∈ S, x s = s)
    (hUsq : ∀ u ∈ U, u * u = 1) (hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hUx : ∀ u ∈ U, x * u * x⁻¹ ∈ U ∧ x⁻¹ * u * x ∈ U)
    (hUne : ∃ τ ∈ U, τ ≠ 1) (hU5 : ∀ u ∈ U, ∃ u' ∈ U, u = u' * x * u'⁻¹ * x⁻¹)
    (hxodd : Odd (orderOf x)) : False := by
  classical
  set A : Subgroup (MulAut G) := U ⊔ Subgroup.zpowers x with hAdef
  have hUA : U ≤ A := le_sup_left
  have hxA : x ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxN : x ∈ Subgroup.normalizer (U : Set (MulAut G)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun h => (hUx u h).1, fun h => ?_⟩
    have := (hUx _ h).2
    simpa [mul_assoc] using this
  have hAN : A ≤ Subgroup.normalizer (U : Set (MulAut G)) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hxN)
  have hAfix : ∀ α ∈ A, ∀ s ∈ S, α s = s := by
    have : A ≤ sylowFixingAut S :=
      sup_le (fun u hu => mem_sylowFixingAut.2 (hU u hu))
        (Subgroup.zpowers_le.2 (mem_sylowFixingAut.2 hx))
    exact fun α hα => mem_sylowFixingAut.1 (this hα)
  set B : Subgroup A := U.subgroupOf A with hBdef
  have hBmem : ∀ b : A, b ∈ B ↔ (b : MulAut G) ∈ U := fun b => Iff.rfl
  have hBp : IsPGroup 2 B := by
    intro b
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (Subtype.ext (hUsq b b.2))
  have hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b := fun b hb c hc =>
    Subtype.ext (hUcomm b hb c hc)
  let xA : A := ⟨x, hxA⟩
  have hxB : ∀ b ∈ B, xA * b * xA⁻¹ ∈ B := fun b hb => (hUx b hb).1
  have hxB' : ∀ b ∈ B, xA⁻¹ * b * xA ∈ B := fun b hb => (hUx b hb).2
  obtain ⟨τ, hτU, hτ1⟩ := hUne
  set τA : A := ⟨τ, hUA hτU⟩ with hτA
  have hτB : τA ∈ B := hτU
  have hτA1 : τA ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  have hτA2 : τA * τA = 1 := Subtype.ext (hUsq τ hτU)
  obtain ⟨g, hgH, hgT, hgN⟩ := exists_conj_not_normalizer hG hSp hSi hAfix hBp hτB hτA1 hτA2
  set H := hSub A B with hH
  set T := tSub S A hAfix B with hT
  set τ' : AutExt A := inr τA with hτ'
  set P := Subgroup.zpowers τ' with hP
  have hTH : IsSylowOf 2 T H := isSylowOf_tSub hSp hSi hBp
  have hτ'T : τ' ∈ T := ⟨by simp [hτ'], hτB⟩
  have hZT : ∀ b ∈ B, ∀ t ∈ T, (inr b : AutExt A) * t = t * inr b := fun b hb t ht =>
    inr_comm_of_right_central (hA := hAfix) ht.1 b (hBcomm b hb _ ht.2)
  have hPT : T ≤ Subgroup.normalizer (P : Set (AutExt A)) := fun t ht =>
    mem_normalizer_zpowers_of_commute (show Commute t τ' from (hZT τA hτB t ht).symm)
  have hPleT : P ≤ T := Subgroup.zpowers_le.2 hτ'T
  obtain ⟨Q, ⟨hPQ, hQT, hb, hc, h, hhmem, ⟨r, hr, hr2, n, hord⟩, hhP⟩, hZQ⟩ :=
    lemma1_central hTH hPT hPleT hgH hgT hgN
  have hinrT : ∀ b ∈ B, (inr b : AutExt A) ∈ T := fun b hb =>
    ⟨by rw [left_inr]; exact S.one_mem, hb⟩
  have hinrQ : ∀ b ∈ B, (inr b : AutExt A) ∈ Q := fun b hb =>
    hZQ ⟨hinrT b hb, Subgroup.mem_centralizer_iff.2 fun t ht => (hZT b hb t ht).symm⟩
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => Subtype.ext (hUsq b hb)
  set W : Subgroup (AutExt A) := T ⊓ Subgroup.centralizer (Q : Set (AutExt A)) with hW
  set V : Subgroup (AutExt A) := omegaCenter W with hV
  set Gk : Subgroup (AutExt A) := (rightHom : AutExt A →* A).ker with hGk
  have hGkn : Gk.Normal := MonoidHom.normal_ker _
  have hGkN : ∀ g : AutExt A, g ∈ Subgroup.normalizer (Gk : Set (AutExt A)) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hGkn.conj_mem y hy g, fun hy => by
      have := hGkn.conj_mem _ hy g⁻¹
      simpa [mul_assoc] using this⟩
  set W' : Subgroup (AutExt A) := V ⊓ Gk with hW'
  set U'' : Subgroup (AutExt A) := B.map inr with hU''
  set E : Subgroup (AutExt A) := T ⊓ Subgroup.normalizer (Q : Set (AutExt A)) with hE
  set J : Subgroup (AutExt A) :=
    Subgroup.normalizer (Q : Set (AutExt A)) ⊓ Subgroup.normalizer (W : Set (AutExt A)) with hJ
  have hinrW : ∀ b ∈ B, (inr b : AutExt A) ∈ W := fun b hb =>
    ⟨hinrT b hb, Subgroup.mem_centralizer_iff.2 fun q hq => (hZT b hb q (hQT hq)).symm⟩
  have hinrV : ∀ b ∈ B, (inr b : AutExt A) ∈ V := fun b hb =>
    ⟨hinrW b hb, fun w hw => (hZT b hb w hw.1).symm, by rw [← map_mul, hBsq b hb, map_one]⟩
  have hU''V : U'' ≤ V := by
    rintro _ ⟨b, hb, rfl⟩
    exact hinrV b hb
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hb.2.1 a ha.1
  have hVp : IsPGroup 2 V := by
    intro v
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext v.2.2.2
  have hWT : W ≤ T := inf_le_left
  have hxKQ : (inr xA : AutExt A) ∈ Subgroup.normalizer (Q : Set (AutExt A)) :=
    inr_mem_normalizer_of_inr_le (hA := hAfix) hxB hxB' hQT hinrQ
  have hxKW : (inr xA : AutExt A) ∈ Subgroup.normalizer (W : Set (AutExt A)) :=
    inr_mem_normalizer_of_inr_le (hA := hAfix) hxB hxB' hWT hinrW
  have hxKJ : (inr xA : AutExt A) ∈ J := ⟨hxKQ, hxKW⟩
  have hhH : h ∈ H := hhmem.1.1
  have hhJ : h ∈ J := ⟨hhmem.1.2, hhmem.2⟩
  have hhr : rightHom h = 1 := by
    have h1 : orderOf (rightHom h) ∣ orderOf h := orderOf_map_dvd rightHom h
    have hhB : rightHom h ∈ B := hhH
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hBp ⟨rightHom h, hhB⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk, hord] at h1
    have hcop : Nat.Coprime (2 ^ k) (r ^ n) :=
      Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hr).2 hr2.symm)
    have h2 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd hcop h1
    rw [h2] at hk
    exact orderOf_eq_one_iff.1 hk
  have hhGk : h ∈ Gk := hhr
  have hJV : J ≤ Subgroup.normalizer (V : Set (AutExt A)) := fun j hj =>
    mem_normalizer_omegaCenter hj.2
  have hJW' : J ≤ Subgroup.normalizer (W' : Set (AutExt A)) := fun j hj =>
    mem_normalizer_inf (hJV hj) (hGkN j)
  have hBn : B.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUA).2 hAN
  have hHn : H.Normal := hBn.comap rightHom
  have hBsup : B ⊔ Subgroup.zpowers xA = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hUA, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hBidx : ¬ 2 ∣ B.index := by
    have h1 : B.relIndex (B ⊔ Subgroup.zpowers xA) = B.relIndex (Subgroup.zpowers xA) :=
      Subgroup.relIndex_sup_left (Subgroup.zpowers xA) B
    rw [hBsup, Subgroup.relIndex_top_right] at h1
    have hox : orderOf xA = orderOf x := (Subgroup.orderOf_coe xA).symm
    have h2 : B.relIndex (Subgroup.zpowers xA) ∣ orderOf x := by
      have := Subgroup.index_dvd_card (B.subgroupOf (Subgroup.zpowers xA))
      rw [Nat.card_zpowers, hox] at this
      exact this
    rw [← h1] at h2
    exact fun hd => (Nat.not_even_iff_odd.2 hxodd) (even_iff_two_dvd.2 (hd.trans h2))
  have hRidx : ¬ 2 ∣ E.relIndex J := by
    have hEHJ : E ≤ H ⊓ Subgroup.normalizer (Q : Set (AutExt A)) ⊓
        Subgroup.normalizer (W : Set (AutExt A)) :=
      le_inf (inf_le_inf_right _ (hTH.le)) (inf_normalizer_le_normalizer_inf_centralizer T Q)
    have hHJJ : H ⊓ Subgroup.normalizer (Q : Set (AutExt A)) ⊓
        Subgroup.normalizer (W : Set (AutExt A)) ≤ J := le_inf
      (inf_le_left.trans inf_le_right) inf_le_right
    have h1 : ¬ 2 ∣ E.relIndex (H ⊓ Subgroup.normalizer (Q : Set (AutExt A)) ⊓
        Subgroup.normalizer (W : Set (AutExt A))) := ((isSylowOf_iff).1 hc).2.2
    have h2 : (H ⊓ Subgroup.normalizer (Q : Set (AutExt A)) ⊓
        Subgroup.normalizer (W : Set (AutExt A))).relIndex J ∣ H.index := by
      have e : H ⊓ Subgroup.normalizer (Q : Set (AutExt A)) ⊓
          Subgroup.normalizer (W : Set (AutExt A)) = H ⊓ J := by rw [hJ, inf_assoc]
      rw [e, Subgroup.inf_relIndex_right]
      exact Subgroup.relIndex_dvd_index_of_normal H J
    have h3 : H.index = B.index := Subgroup.index_comap_of_surjective B rightHom_surjective
    rw [h3] at h2
    have h4 := Subgroup.relIndex_mul_relIndex E _ J hEHJ hHJJ
    rw [← h4]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with hd | hd
    · exact h1 hd
    · exact hBidx (hd.trans h2)
  have hdec : ∀ v ∈ V, (inl v.left : AutExt A) ∈ W' ∧ (inr v.right : AutExt A) ∈ U'' ∧
      v = inl v.left * inr v.right := by
    intro v hv
    have hvT : v ∈ T := hv.1.1
    have h1 : (inr v.right : AutExt A) ∈ U'' := ⟨v.right, hvT.2, rfl⟩
    have h2 : (inl v.left : AutExt A) = v * (inr v.right)⁻¹ := by
      calc (inl v.left : AutExt A) = (inl v.left * inr v.right) * (inr v.right)⁻¹ := by group
        _ = v * (inr v.right)⁻¹ := by rw [← inl_inr_decomp v]
    refine ⟨⟨?_, ?_⟩, h1, inl_inr_decomp v⟩
    · rw [h2]
      exact V.mul_mem hv (V.inv_mem (hU''V h1))
    · show rightHom (inl v.left : AutExt A) = 1
      exact rightHom_inl _
  have hWU : W' ⊓ U'' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨_, hyG⟩, b, hb, rfl⟩
    have : b = 1 := by
      have h1 : rightHom (inr b : AutExt A) = 1 := hyG
      rwa [rightHom_inr] at h1
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hWU' : W' ⊔ U'' = V := by
    refine le_antisymm (sup_le inf_le_left hU''V) fun v hv => ?_
    obtain ⟨h1, h2, h3⟩ := hdec v hv
    rw [h3]
    exact Subgroup.mul_mem_sup h1 h2
  have hRU : E ≤ Subgroup.normalizer (U'' : Set (AutExt A)) := by
    intro e he
    apply mem_normalizer_of_commute
    rintro _ ⟨b, hb, rfl⟩
    exact (hZT b hb e he.1).symm
  obtain ⟨U₀, hU₀V, hJU₀, hWU₀, hWU₀'⟩ := exists_invariant_complement_subgroup (p := 2) V W' J E
    U'' hVcomm hVp inf_le_left hJV hJW' hRidx hRU hU''V hWU hWU'
  have hxKU₀ : (inr xA : AutExt A) ∈ Subgroup.normalizer (U₀ : Set (AutExt A)) := hJU₀ hxKJ
  have hxKV : (inr xA : AutExt A) ∈ Subgroup.normalizer (V : Set (AutExt A)) := hJV hxKJ
  have hVcl : ∀ y ∈ Subgroup.closure ((W' : Set (AutExt A)) ∪ (U₀ : Set (AutExt A))), y ∈ V := by
    intro y hy
    rw [← Subgroup.sup_eq_closure, hWU₀'] at hy
    exact hy
  have hcV : ∀ y ∈ V, (inr xA : AutExt A) * y⁻¹ * (inr xA)⁻¹ ∈ V := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 hxKV y⁻¹).1 (V.inv_mem hy)
  have hκ' : ∀ v ∈ Subgroup.closure ((W' : Set (AutExt A)) ∪ (U₀ : Set (AutExt A))),
      v * inr xA * v⁻¹ * (inr xA)⁻¹ ∈ U₀ := by
    intro v hv'
    induction hv' using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      ·
        have hyT : y ∈ T := hy.1.1.1
        have hyr : y.right = 1 := hy.2
        have hcomm : (inr xA : AutExt A) * y = y * inr xA :=
          inr_comm_of_right_central (hA := hAfix) hyT.1 xA (by rw [hyr, mul_one, one_mul])
        have : y * inr xA * y⁻¹ * (inr xA)⁻¹ = 1 := by
          rw [← hcomm]
          group
        rw [this]
        exact U₀.one_mem
      · have := (Subgroup.mem_normalizer_iff.1 hxKU₀ y⁻¹).1 (U₀.inv_mem hy)
        have e : y * inr xA * y⁻¹ * (inr xA)⁻¹ = y * ((inr xA : AutExt A) * y⁻¹ * (inr xA)⁻¹) := by
          group
        rw [e]
        exact U₀.mul_mem hy this
    | one => simp
    | mul y z hy hz ihy ihz =>
      have hyV := hVcl y hy
      have hzV := hVcl z hz
      have hcy := hcV y hyV
      have hcz := hcV z hzV
      have e : y * z * inr xA * (y * z)⁻¹ * (inr xA)⁻¹ =
          (y * inr xA * y⁻¹ * (inr xA)⁻¹) * (z * inr xA * z⁻¹ * (inr xA)⁻¹) := by
        calc y * z * inr xA * (y * z)⁻¹ * (inr xA)⁻¹
            = y * z * ((inr xA : AutExt A) * z⁻¹ * (inr xA)⁻¹) *
                ((inr xA : AutExt A) * y⁻¹ * (inr xA)⁻¹) := by group
          _ = y * (z * ((inr xA : AutExt A) * z⁻¹ * (inr xA)⁻¹)) *
                ((inr xA : AutExt A) * y⁻¹ * (inr xA)⁻¹) := by group
          _ = y * (((inr xA : AutExt A) * y⁻¹ * (inr xA)⁻¹) *
                (z * ((inr xA : AutExt A) * z⁻¹ * (inr xA)⁻¹))) := by
              rw [mul_assoc, hVcomm _ (V.mul_mem hzV hcz) _ hcy]
          _ = (y * inr xA * y⁻¹ * (inr xA)⁻¹) * (z * inr xA * z⁻¹ * (inr xA)⁻¹) := by group
      rw [e]
      exact U₀.mul_mem ihy ihz
    | inv y hy ih =>
      have hyV := hVcl y hy
      have hcy : (inr xA : AutExt A) * y * (inr xA)⁻¹ ∈ V := by
        have := hcV y⁻¹ (V.inv_mem hyV)
        simpa using this
      have e : y⁻¹ * inr xA * y⁻¹⁻¹ * (inr xA)⁻¹ =
          (y * inr xA * y⁻¹ * (inr xA)⁻¹)⁻¹ := by
        calc y⁻¹ * inr xA * y⁻¹⁻¹ * (inr xA)⁻¹
            = y⁻¹ * ((inr xA : AutExt A) * y * (inr xA)⁻¹) := by group
          _ = ((inr xA : AutExt A) * y * (inr xA)⁻¹) * y⁻¹ := hVcomm _ (V.inv_mem hyV) _ hcy
          _ = (y * inr xA * y⁻¹ * (inr xA)⁻¹)⁻¹ := by group
      rw [e]
      exact U₀.inv_mem ih
  have hκ : ∀ v ∈ V, v * inr xA * v⁻¹ * (inr xA)⁻¹ ∈ U₀ := fun v hv => hκ' v (by
    rw [← Subgroup.sup_eq_closure, hWU₀']
    exact hv)
  have hU''U₀ : U'' ≤ U₀ := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨u', hu'U, hu'⟩ := hU5 b hb
    let b' : A := ⟨u', hUA hu'U⟩
    have hb'B : b' ∈ B := hu'U
    have hbb' : b = b' * xA * b'⁻¹ * xA⁻¹ := Subtype.ext hu'
    have := hκ (inr b') (hinrV b' hb'B)
    rw [hbb', map_mul, map_mul, map_mul, map_inv, map_inv]
    exact this
  have hU₀U'' : U₀ ≤ U'' := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := hdec u (hU₀V hu)
    have h4 : (inl u.left : AutExt A) ∈ U₀ := by
      have : (inl u.left : AutExt A) = u * (inr u.right)⁻¹ := by
        calc (inl u.left : AutExt A) = (inl u.left * inr u.right) * (inr u.right)⁻¹ := by group
          _ = u * (inr u.right)⁻¹ := by rw [← inl_inr_decomp u]
      rw [this]
      exact U₀.mul_mem hu (U₀.inv_mem (hU''U₀ h2))
    have h5 : (inl u.left : AutExt A) ∈ W' ⊓ U₀ := ⟨h1, h4⟩
    rw [hWU₀, Subgroup.mem_bot] at h5
    rw [h3, h5, one_mul]
    exact h2
  have hU₀eq : U₀ = U'' := le_antisymm hU₀U'' hU''U₀
  have hhN : h ∈ Subgroup.normalizer (U'' : Set (AutExt A)) := by
    rw [← hU₀eq]
    exact hJU₀ hhJ
  have hτ'U : τ' ∈ U'' := ⟨τA, hτB, rfl⟩
  have hz1 : τ'⁻¹ * h⁻¹ * τ' * h ∈ U'' := by
    have h1 : h⁻¹ * τ' * h ∈ U'' := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hhN) τ').1 hτ'U
      simpa using this
    have := U''.mul_mem (U''.inv_mem hτ'U) h1
    simpa [mul_assoc] using this
  have hz2 : τ'⁻¹ * h⁻¹ * τ' * h ∈ Gk := by
    show rightHom (τ'⁻¹ * h⁻¹ * τ' * h) = 1
    have hhr' : h.right = 1 := hhr
    simp [hhr']
  have hz3 : τ'⁻¹ * h⁻¹ * τ' * h ∈ U'' ⊓ Gk := ⟨hz1, hz2⟩
  have hUGk : U'' ⊓ Gk = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨b, hb, rfl⟩, hyG⟩
    have : b = 1 := by
      have h1 : rightHom (inr b : AutExt A) = 1 := hyG
      rwa [rightHom_inr] at h1
    rw [this, map_one]
    exact Subgroup.one_mem _
  rw [hUGk, Subgroup.mem_bot] at hz3
  apply hhP
  apply mem_normalizer_zpowers_of_commute
  have hz4 : τ'⁻¹ * h⁻¹ * τ' * h = 1 := hz3
  calc h * τ' = h * τ' * (τ'⁻¹ * h⁻¹ * τ' * h) := by rw [hz4, mul_one]
    _ = τ' * h := by group

end Main

end CFSG.ClassicalInvolution.GlaubermanAut
