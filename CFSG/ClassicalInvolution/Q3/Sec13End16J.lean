module

public import CFSG.ClassicalInvolution.Q3.Sec13End16I

import CFSG.ClassicalInvolution.Q3.Sec13End15G

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin hiding centMembers

variable {G : Type} [Group G] [Finite G]

namespace Sit16

variable {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem natCard_lambdaW_eq_two (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nat.card (lambdaW Ω W) = 2 := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hu : u ∈ zGroup Ω := (u_mem_zGroup c h h9 h13).1
  have hO : classicalInvolutionOddCore ↥(pSpan (centMembers Ω u)) = ⊥ :=
    EndHyp.oddCore_centMembers_eq_bot h h9 c.twin h13 hu c.data.hu1
  obtain ⟨I⟩ := exists_aeIdent_five_Y c h h9 h13
  have hY : pSpan (centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun L hL => hL.2
  have hinv : ∀ L ∈ centMembers Ω u, ∀ x ∈ pSpan (centMembers Ω u),
      conjSub x L ∈ centMembers Ω u := by
    intro L hL x hx
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hY hx)
    have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant hL
      (n := x)
    rwa [show x * u * x⁻¹ = u by rw [hxu, mul_inv_cancel_right]] at hc
  have hJ : conjSub g K ∈ centMembers Ω u :=
    ⟨((c.conjSub_mem h h9).2.1).1, (c.conjSub_le_centralizer_u h h9).1⟩
  have hA : ∀ d ∈ lambdaW Ω W, (∀ L ∈ centMembers Ω u, conjSub d L ∈ centMembers Ω u) ∧
      ∀ L ∈ centMembers Ω u, ∀ r : G, IsUniqueInvolution L r → d * r = r * d := by
    intro d hd
    have hdD : d ∈ zGroup Ω := (Subgroup.mem_inf.mp hd).1
    have hdu : d * u = u * d := h.zGroup_comm h9 d hdD u hu
    refine ⟨fun L hL => ?_, fun L hL r hr => ?_⟩
    · have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant hL
        (n := d)
      rwa [show d * u * d⁻¹ = u by rw [hdu, mul_inv_cancel_right]] at hc
    · have hrD : r ∈ zGroup Ω := Subgroup.subset_closure ⟨L, hL.1, hr⟩
      exact h.zGroup_comm h9 d hdD r hrD
  have hAL : ∀ a ∈ lambdaW Ω W, ∀ l ∈ conjSub g K, a * l = l * a := by
    intro a ha l hl
    have haJ : a ∈ Subgroup.centralizer ((conjSub g K : Subgroup G) : Set G) := by
      rw [lambdaW_eq c h h9 h13] at ha
      exact (Subgroup.mem_inf.mp ha).2
    exact (Subgroup.mem_centralizer_iff.mp haJ l hl).symm
  have hbound := natCard_le_of_aeIdent hΩ h.thmD.two (fun L hL => hL.1) hinv
    (by norm_num) (by norm_num) I (I.toLabel.isPGroup_ker hO) hA hJ hAL
  have hsub : lambdaW Ω W ⊓ Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G)
      = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxL : x ∈ lambdaW Ω W := (Subgroup.mem_inf.mp hx).1
    have hxY : x ∈ Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    have hxX : x ∈ Subgroup.centralizer ((pSpan (centMembers Ω e) : Subgroup G) : Set G) := by
      rw [lambdaW_eq_centralizer c h h9 h13] at hxL
      exact (Subgroup.mem_inf.mp hxL).2
    have hXY : pSpan (centMembers Ω e) ⊔ pSpan (centMembers Ω u) ≤
        Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxX s hs)
      · exact fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hxY s hs)
    rw [pSpan_sup_eq_top_of_X c h h9 h13] at hXY
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g'
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hXY (Subgroup.mem_top g')))
    rw [h.center] at hxc
    exact hxc
  have hcard1 : Nat.card ↥(lambdaW Ω W ⊓
      Subgroup.centralizer ((pSpan (centMembers Ω u) : Subgroup G) : Set G)) = 1 := by
    rw [hsub, Subgroup.card_bot]
  have hle : Nat.card ↥(lambdaW Ω W) ≤ 2 := by
    rw [hcard1] at hbound
    simpa using hbound
  have hge : 2 ≤ Nat.card ↥(lambdaW Ω W) := by
    haveI : Nontrivial ↥(lambdaW Ω W) :=
      ⟨⟨⟨e, e_mem_lambdaW c h h9 h13⟩, 1, fun h' => c.data.he1 (congrArg Subtype.val h')⟩⟩
    exact Finite.one_lt_card
  omega

theorem natCard_zGroup_eq_sixtyFour_of_frame
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    Nat.card (zGroup Ω) = 64 ∧ Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) = 8 ∧
      ∃ d ∈ zGroup Ω ⊓ Subgroup.centralizer (K : Set G),
        d ∉ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  have hL := natCard_lambdaW_eq_two c h h9 h13
  obtain ⟨ε, hε, hD, hiff⟩ := c.natCard_zGroup_eq_sixteen_mul h h9 h13
  have hE : ¬ eGroup Ω K ≤ K ⊔ K' := fun hle =>
    (c.mul_mem_eGroup h h9).2 (hle (c.mul_mem_eGroup h h9).1)
  have h64 := EndHyp.sixtyFour_le_natCard_zGroup h h9 c.twin h13 hE
  have h8 := EndHyp.natCard_zGroup_eq_eight_mul h h9 c.twin h13
  rw [hL] at hD
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hε
  have hε2 : ε = 2 := by
    rcases hε with rfl | rfl
    · omega
    · rfl
  subst hε2
  have hD64 : Nat.card (zGroup Ω) = 64 := by omega
  exact ⟨hD64, by omega, hiff.mp rfl⟩

private theorem e16j_comm_of_unique {K : Subgroup G} {q : G} (hq : IsUniqueInvolution K q)
    {x : G} (hx : x ∈ K) : x * q = q * x := by
  have hy : x * q * x⁻¹ ∈ K := K.mul_mem (K.mul_mem hx hq.mem) (K.inv_mem hx)
  have hsq : x * q * x⁻¹ * (x * q * x⁻¹) = 1 := by
    calc x * q * x⁻¹ * (x * q * x⁻¹) = x * (q * q) * x⁻¹ := by group
      _ = 1 := by rw [hq.sq]; group
  rcases hq.unique _ hy hsq with h1 | h1
  · have h2 : x * q = x := mul_inv_eq_one.mp h1
    exact absurd (mul_left_cancel (h2.trans (mul_one x).symm)) hq.ne_one
  · calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [h1]

private theorem e16j_injective_of_card {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (h : Nat.card A = Nat.card f.range) : Function.Injective f := by
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, ← h] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h2 : Nat.card f.ker = 1 := by
    have h3 : Nat.card f.ker * Nat.card A = 1 * Nat.card A := by rw [one_mul]; exact h1
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  exact (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.eq_bot_of_card_eq f.ker h2)

private theorem e16j_comm_memBar {n : ℕ} (α : Finset (Fin n)) (hα : α.card = 4) (b₁ b₂ : Bool)
    (hne : b₁ ≠ b₂) : ∀ x ∈ AE.memBar α hα b₁, ∀ y ∈ AE.memBar α hα b₂, x * y = y * x := by
  cases b₁ <;> cases b₂
  · exact absurd rfl hne
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, (AE.comm_memK_memKStar (AE.emb α hα) c hc a ha).symm]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, AE.comm_memK_memKStar (AE.emb α hα) a ha c hc]
  · exact absurd rfl hne

private theorem e16j_kList_fix : ∀ k ∈ AE.kList, ∀ j : Fin 4, k.perm j = j → k.perm = 1 := by
  decide +kernel

private theorem e16j_kStarList_fix :
    ∀ k ∈ AE.kStarList, ∀ j : Fin 4, k.perm j = j → k.perm = 1 := by
  decide +kernel

private theorem e16j_memAt_perm {α : Finset (Fin 5)} {h : α.card = 4} {b : Bool}
    {a : AE.Wr 5} (ha : a ∈ AE.memAt α h b) {x : Fin 5} (hx : x ∈ α) (hfix : a.perm x = x) :
    a.perm = 1 := by
  have hr : x ∈ Set.range (AE.emb α h) := by
    rw [AE.range_emb]
    exact Finset.mem_coe.mpr hx
  obtain ⟨j, rfl⟩ := hr
  cases b
  · obtain ⟨k, hk, rfl⟩ := (show a ∈ AE.memKStar (AE.emb α h) from ha)
    have hk1 : k.perm j = j := by
      have h1 := hfix
      rw [AE.embed_perm, AE.embedPerm_apply] at h1
      exact (AE.emb α h).injective h1
    rw [AE.embed_perm, e16j_kStarList_fix k (AE.mem_kQStar.mp hk) j hk1, AE.embedPerm_one]
  · obtain ⟨k, hk, rfl⟩ := (show a ∈ AE.memK (AE.emb α h) from ha)
    have hk1 : k.perm j = j := by
      have h1 := hfix
      rw [AE.embed_perm, AE.embedPerm_apply] at h1
      exact (AE.emb α h).injective h1
    rw [AE.embed_perm, e16j_kList_fix k (AE.mem_kQ.mp hk) j hk1, AE.embedPerm_one]

private theorem e16j_memAt_ne_one (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool) :
    ∃ c ∈ AE.memAt α h b, c.perm ≠ 1 := by
  have key : ∀ j : Fin 4, AE.d₁ j ≠ j := by decide +kernel
  have hne1 : AE.embedPerm (AE.emb α h) AE.d₁ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 5) => σ (AE.emb α h 0)) h1
    simp only [AE.embedPerm_apply, Equiv.Perm.one_apply] at h2
    exact key 0 ((AE.emb α h).injective h2)
  cases b
  · exact ⟨AE.embed (AE.emb α h) ⟨AE.vec4 [0, 3], AE.d₁⟩,
      ⟨⟨AE.vec4 [0, 3], AE.d₁⟩, AE.mem_kQStar.mpr (by decide +kernel), rfl⟩,
      by rw [AE.embed_perm]; exact hne1⟩
  · exact ⟨AE.embed (AE.emb α h) ⟨AE.vec4 [0, 2], AE.d₁⟩,
      ⟨⟨AE.vec4 [0, 2], AE.d₁⟩, AE.mem_kQ.mpr (by decide +kernel), rfl⟩,
      by rw [AE.embed_perm]; exact hne1⟩

private theorem e16j_ae5_not_normalizing {α β : Finset (Fin 5)} (hα : α.card = 4)
    (hβ : β.card = 4) (hne : α ≠ β) (b b' : Bool) {x : AE.AEQ 5}
    (hx : x ∈ AE.memBar β hβ b') (hx2 : x * x ≠ 1)
    (hn : ∀ y ∈ AE.memBar α hα b, x * y * x⁻¹ ∈ AE.memBar α hα b) : False := by
  obtain ⟨a, ha, rfl⟩ := hx
  have ha2 : a * a ≠ 1 := fun h => hx2 (by rw [← map_mul, h, map_one])
  obtain ⟨p, hpβ, hpα⟩ : ∃ p, p ∈ β ∧ p ∉ α := by
    by_contra hcon
    have hsub : β ⊆ α := fun q hq => by
      by_contra hqα
      exact hcon ⟨q, hq, hqα⟩
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hcompl : ∀ t : Fin 5, t ∉ α → t = p := by
    have key : ∀ γ : Finset (Fin 5), γ.card = 4 → ∀ t u : Fin 5, t ∉ γ → u ∉ γ → t = u := by
      decide +kernel
    exact fun t ht => key α hα t p ht hpα
  have hpr : p ∉ Set.range (AE.emb α hα) := by
    rw [AE.range_emb]
    exact fun h' => hpα (Finset.mem_coe.mp h')
  have hperm : ∀ c ∈ AE.memAt α hα b, c.perm (a.perm⁻¹ p) = a.perm⁻¹ p := by
    intro c hc
    have hmem : AE.mkQ 5 (a * c * a⁻¹) ∈ AE.memBar α hα b := by
      have h1 := hn (AE.mkQ 5 c) ⟨c, hc, rfl⟩
      simpa only [map_mul, map_inv] using h1
    obtain ⟨d, hd, hdeq⟩ := hmem
    have h0 : (d⁻¹ * (a * c * a⁻¹)).perm = 1 := by
      rcases AE.mkQ_eq_iff.mp hdeq with h1 | h1 <;> rw [h1] <;> rfl
    have hw : d.perm = (a * c * a⁻¹).perm := by
      rw [AE.Wr.mul_perm, AE.Wr.inv_perm] at h0
      exact inv_mul_eq_one.mp h0
    have hdp : d.perm p = p := ((AE.supportedOn_of_mem_memAt hd) p hpr).2
    have hw2 : (a * c * a⁻¹).perm p = p := by
      rw [← hw]
      exact hdp
    rw [AE.Wr.mul_perm, AE.Wr.mul_perm, AE.Wr.inv_perm, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply] at hw2
    calc c.perm (a.perm⁻¹ p) = a.perm⁻¹ (a.perm (c.perm (a.perm⁻¹ p))) := by simp
      _ = a.perm⁻¹ p := by rw [hw2]
  by_cases hs : a.perm⁻¹ p ∈ α
  · obtain ⟨c, hc, hc1⟩ := e16j_memAt_ne_one α hα b
    exact hc1 (e16j_memAt_perm hc hs (hperm c hc))
  · have hsp : a.perm⁻¹ p = p := hcompl _ hs
    have hfix : a.perm p = p := by
      have h1 : a.perm (a.perm⁻¹ p) = p := by simp
      rw [hsp] at h1
      exact h1
    have ha1 : a.perm = 1 := e16j_memAt_perm ha hpβ hfix
    exact ha2 (AE.vecSub_mul_self (show a ∈ AE.vecSub 5 from ha1))

private theorem e16j_dSet_line (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω)
    (h13 : zGroup Ω ≠ eGroup Ω K) {r : G} (hr : r = z ∨ r = u * e ∨ r = z * (u * e)) :
    ∃ R ∈ DSet Ω W, IsUniqueInvolution R r := by
  rcases hr with h1 | h1 | h1
  · exact ⟨K, h.mem_dSet_of_mem c.data.hW c.twin.mem c.twin.isInv c.data.hzW,
      by rw [h1]; exact c.twin.isInv⟩
  · exact ⟨conjSub g K, (c.conjSub_mem h h9).1,
      by rw [h1]; exact (c.conjSub_mem h h9).2.2.2⟩
  · obtain ⟨R, hR, hRi⟩ := c.exists_dSet_zt h h9
    exact ⟨R, hR, by rw [h1]; exact hRi⟩

private theorem e16j_aeIdent_line (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) {r : G}
    (hr : r = z ∨ r = u * e ∨ r = z * (u * e)) :
    Nonempty (AEIdent (centMembers Ω (e * r)) 5) := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hd := c.data
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := by
    have hs := Subgroup.subset_closure (Set.mem_singleton e)
    rw [hd.he] at hs
    exact (Subgroup.mem_inf.mp hs).1
  have hid : e * (u * e) = u := by
    calc e * (u * e) = (e * u) * e := by rw [mul_assoc]
      _ = (u * e) * e := by rw [hWab e heW u hd.huW]
      _ = u * (e * e) := by rw [mul_assoc]
      _ = u := by rw [hd.he2, mul_one]
  rcases hr with h1 | h1 | h1
  · rw [h1]
    exact exists_aeIdent_five_Y (c.conj_frame h h9) h h9
      (h.zGroup_ne_eGroup_conj c.twin.mem h13 g)
  · rw [h1, hid]
    exact exists_aeIdent_five_Y c h h9 h13
  · obtain ⟨g₂, c₂⟩ := c.exists_frame_mul_z h h9
    have hid2 : e * (z * (u * e)) = u * z := by
      calc e * (z * (u * e)) = (e * z) * (u * e) := by rw [mul_assoc]
        _ = (z * e) * (u * e) := by rw [hWab e heW z hd.hzW]
        _ = z * (e * (u * e)) := by rw [mul_assoc]
        _ = z * u := by rw [hid]
        _ = u * z := hWab z hd.hzW u hd.huW
    rw [h1, hid2]
    exact exists_aeIdent_five_Y c₂ h h9 h13

private theorem e16j_map_conjSub {P : Set (Subgroup G)} (I : AEIdent P 5) {L : Subgroup G}
    {x : G} (hx : x ∈ pSpan P)
    (hcomm : ∀ y ∈ (L.subgroupOf (pSpan P)).map I.φ, I.φ ⟨x, hx⟩ * y = y * I.φ ⟨x, hx⟩) :
    Subgroup.map I.φ ((conjSub x L).subgroupOf (pSpan P)) =
      Subgroup.map I.φ (L.subgroupOf (pSpan P)) := by
  have hxinv : x⁻¹ ∈ pSpan P := (pSpan P).inv_mem hx
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : x⁻¹ * (a : G) * x ∈ L := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp ha)
    set l : pSpan P := ⟨x⁻¹ * (a : G) * x, (pSpan P).mul_mem ((pSpan P).mul_mem hxinv a.2) hx⟩
      with hl
    have hlmem : I.φ l ∈ (L.subgroupOf (pSpan P)).map I.φ :=
      ⟨l, Subgroup.mem_subgroupOf.mpr ha', rfl⟩
    have hc := hcomm _ hlmem
    have hae : I.φ a = I.φ ⟨x, hx⟩ * I.φ l * (I.φ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [hl, mul_assoc]
    exact ⟨l, Subgroup.mem_subgroupOf.mpr ha', by rw [hae, hc, mul_inv_cancel_right]⟩
  · rintro ⟨l, hl, rfl⟩
    have hlL : x * (l : G) * x⁻¹ ∈ conjSub x L := mem_conjSub_iff.mpr (by
      have : x⁻¹ * (x * (l : G) * x⁻¹) * x = (l : G) := by group
      rw [this]; exact Subgroup.mem_subgroupOf.mp hl)
    set a : pSpan P := ⟨x * (l : G) * x⁻¹, (pSpan P).mul_mem ((pSpan P).mul_mem hx l.2) hxinv⟩
      with ha_def
    refine ⟨a, Subgroup.mem_subgroupOf.mpr hlL, ?_⟩
    have hc := hcomm _ ⟨l, hl, rfl⟩
    have hae : I.φ a = I.φ ⟨x, hx⟩ * I.φ l * (I.φ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [hae, hc, mul_inv_cancel_right]

private theorem e16j_ae5_false {P : Set (Subgroup G)} (h : EndHyp Ω) (h9 : Perp9 Ω)
    (hP : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (I : AEIdent P 5)
    {M R : Subgroup G} {p r : G} (hMP : M ∈ P) (hRP : R ∈ P)
    (hpM : IsUniqueInvolution M p) (hr : IsUniqueInvolution R r) (hpr : p ≠ r)
    (hOm : M ∈ omegaStarNbr Ω R) : False := by
  obtain ⟨α, hα, b, hlabR⟩ := I.label R hRP
  obtain ⟨β, hβ, b', hlabM⟩ := I.label M hMP
  have hMΩ : M ∈ Ω := hP hMP
  have hRΩ : R ∈ Ω := hP hRP
  have hMR : M ≠ R := fun hMR => hpr (hpM.eq (hMR ▸ hr))
  by_cases hαβ : α = β
  · subst hαβ
    by_cases hbb : b = b'
    · subst hbb
      have hmap : Subgroup.map I.φ (R.subgroupOf (pSpan P))
          = Subgroup.map I.φ (M.subgroupOf (pSpan P)) := by rw [hlabR, hlabM]
      exact hMR (h.toStarHyp.aeIdent_map_injective hP I hRP hMP hmap).symm
    ·
      have hbb' : b' ≠ b := fun e => hbb e.symm
      have hMN : ∀ x ∈ M, x ∈ Subgroup.normalizer (R : Set G) := by
        intro x hx
        rw [mem_normalizer_iff_conjSub_eq]
        have hxP : x ∈ pSpan P := le_pSpan hMP hx
        have hc : conjSub x R ∈ P := hinv R hRP x hxP
        refine h.toStarHyp.aeIdent_map_injective hP I hc hRP ?_
        apply e16j_map_conjSub I hxP
        intro y hy
        rw [hlabR] at hy
        have hxφ : I.φ ⟨x, hxP⟩ ∈ AE.memBar α hα b' := by
          rw [← hlabM]; exact I.mem_map hMP hx
        exact e16j_comm_memBar α hα b' b hbb' _ hxφ y hy
      have hMK : M ∈ KPerp Ω R :=
        Set.mem_insert_of_mem R ⟨hMΩ, hMR, M, perpW_mem_RSet h hMΩ, le_rfl, hMN⟩
      rw [h.kPerp_eq_twinSet_of_perp9 h9 hRΩ] at hMK
      obtain ⟨-, z', hz'R, hz'M⟩ := hMK
      exact hpr ((hpM.eq hz'M).trans (hr.eq hz'R).symm)
  ·
    obtain ⟨-, -, U, hU, hUM, hUN⟩ := hOm
    obtain ⟨S, hS, hUS, hUcyc, hrel⟩ := hU
    haveI := hUcyc
    have hS8 : Nat.card S = 8 := perpW_card_of_mem_RSet h hS
    have hU4 : Nat.card U = 4 := by
      have hm := Subgroup.relIndex_mul_card U S
      rw [inf_eq_left.mpr hUS, hrel, hS8] at hm
      omega
    obtain ⟨g0, hg0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    rw [hU4] at hg0
    have hgM : (g0 : G) ∈ M := hUM g0.2
    have hgN : (g0 : G) ∈ Subgroup.normalizer (R : Set G) := hUN g0.2
    have hg2 : (g0 : G) * g0 ≠ 1 := by
      intro h1
      have hdvd : orderOf (g0 : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
      rw [Subgroup.orderOf_coe, hg0] at hdvd
      norm_num at hdvd
    have hcardM : Nat.card (M.subgroupOf (pSpan P)) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_pSpan hMP)).toEquiv]
      exact h.card_eq_eight hMΩ
    have hinj : Function.Injective (I.φ.comp (M.subgroupOf (pSpan P)).subtype) := by
      apply e16j_injective_of_card
      have hrg : (I.φ.comp (M.subgroupOf (pSpan P)).subtype).range
          = (M.subgroupOf (pSpan P)).map I.φ := by
        ext y
        simp [MonoidHom.mem_range, Subgroup.mem_map]
      rw [hrg, hlabM, AE.natCard_memBar (le_refl 5), hcardM]
    set gP : pSpan P := ⟨(g0 : G), le_pSpan hMP hgM⟩ with hgP
    have hx0mem : I.φ gP ∈ AE.memBar β hβ b' := by
      rw [← hlabM]; exact I.mem_map hMP hgM
    have hx0sq : I.φ gP * I.φ gP ≠ 1 := by
      intro h1
      have h2 : (⟨gP, Subgroup.mem_subgroupOf.mpr hgM⟩ : M.subgroupOf (pSpan P)) *
          ⟨gP, Subgroup.mem_subgroupOf.mpr hgM⟩ = 1 := by
        apply hinj
        show I.φ (gP * gP) = I.φ 1
        rw [map_mul, map_one]
        exact h1
      apply hg2
      have h3 := congrArg (fun t : M.subgroupOf (pSpan P) => ((t : pSpan P) : G)) h2
      simpa [hgP] using h3
    have hnorm : ∀ y ∈ AE.memBar α hα b, I.φ gP * y * (I.φ gP)⁻¹ ∈ AE.memBar α hα b := by
      intro y hy
      rw [← hlabR] at hy ⊢
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨gP * a * gP⁻¹, ?_, by simp [map_mul, map_inv]⟩
      apply Subgroup.mem_subgroupOf.mpr
      have hna : (g0 : G) * (a : G) * (g0 : G)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hgN (a : G)).mp (Subgroup.mem_subgroupOf.mp ha)
      simpa [hgP, mul_assoc] using hna
    exact e16j_ae5_not_normalizing hα hβ hαβ b b' hx0mem hx0sq hnorm

theorem le_centralizer_of_mem_normalizer
    (c : Sit16 Ω K K' W z u e g) (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K)
    {M : Subgroup G} (hM : M ∈ Ω) (heM : e ∈ Subgroup.normalizer (M : Set G)) :
    M ≤ Subgroup.centralizer ({e} : Set G) := by
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  obtain ⟨⟨p, hpM⟩, -⟩ := hΩ.omega1 M hM
  have hpD : p ∈ zGroup Ω := Subgroup.subset_closure ⟨M, hM, hpM⟩
  have hd := c.data
  obtain ⟨huD, heD⟩ := c.u_mem_zGroup h h9 h13
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have htD : u * e ∈ zGroup Ω := (zGroup Ω).mul_mem huD heD
  have heW : e ∈ W := by
    have hs := Subgroup.subset_closure (Set.mem_singleton e)
    rw [hd.he] at hs
    exact (Subgroup.mem_inf.mp hs).1
  have hteW : u * e ∈ W := W.mul_mem hd.huW heW
  have hztW : z * (u * e) ∈ W := W.mul_mem hd.hzW hteW
  by_cases hpℓ : p = z ∨ p = u * e ∨ p = z * (u * e)
  · have hpW : p ∈ W := by
      rcases hpℓ with h1 | h1 | h1 <;> rw [h1]
      exacts [hd.hzW, hteW, hztW]
    exact c.dSet_le_centralizer M (h.mem_dSet_of_mem hd.hW hM hpM hpW)
  · obtain ⟨bf, hbf⟩ := h.exists_endForm h9 c.twin h13
    obtain ⟨Q, hQ, hQ0⟩ : ∃ Q : zGroup Ω, (Q.1 = z ∨ Q.1 = u * e ∨ Q.1 = z * (u * e)) ∧
        bf Q ⟨p, hpD⟩ = 0 := by
      have h3 : bf (⟨z, hzD⟩ * ⟨u * e, htD⟩) ⟨p, hpD⟩
          = bf ⟨z, hzD⟩ ⟨p, hpD⟩ + bf ⟨u * e, htD⟩ ⟨p, hpD⟩ := hbf.mul_left _ _ _
      have h4 : ∀ a b : ZMod 2, a = 0 ∨ b = 0 ∨ a + b = 0 := by decide
      rcases h4 (bf ⟨z, hzD⟩ ⟨p, hpD⟩) (bf ⟨u * e, htD⟩ ⟨p, hpD⟩) with h5 | h5 | h5
      · exact ⟨⟨z, hzD⟩, Or.inl rfl, h5⟩
      · exact ⟨⟨u * e, htD⟩, Or.inr (Or.inl rfl), h5⟩
      · exact ⟨⟨z, hzD⟩ * ⟨u * e, htD⟩, Or.inr (Or.inr rfl), h3.trans h5⟩
    obtain ⟨R, hRD, hRr⟩ := e16j_dSet_line c h h9 h13 hQ
    have hRΩ : R ∈ Ω := ((h.mem_dSet_iff).mp hRD).1
    have hcR : R ≤ Subgroup.centralizer ({e} : Set G) := c.dSet_le_centralizer R hRD
    have hrN : Q.1 ∈ Subgroup.normalizer (M : Set G) :=
      (hbf.spec M hM ⟨p, hpD⟩ hpM Q).mp hQ0
    rcases h.centralizer_or_mul h9 c.twin h13 hRΩ hM hRr hpM heD hcR hrN heM with h1 | h2
    · exact h1
    · exfalso
      obtain ⟨I⟩ := e16j_aeIdent_line c h h9 h13 hQ
      have hpr : p ≠ Q.1 := by
        intro hpr'
        rcases hQ with h6 | h6 | h6
        · exact hpℓ (Or.inl (hpr'.trans h6))
        · exact hpℓ (Or.inr (Or.inl (hpr'.trans h6)))
        · exact hpℓ (Or.inr (Or.inr (hpr'.trans h6)))
      have hRC : R ≤ Subgroup.centralizer ({e * Q.1} : Set G) := by
        intro x hx
        have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hcR hx)
        have hxq : x * Q.1 = Q.1 * x := e16j_comm_of_unique hRr hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * (e * Q.1) = (x * e) * Q.1 := by rw [mul_assoc]
          _ = (e * x) * Q.1 := by rw [hxe]
          _ = e * (x * Q.1) := by rw [mul_assoc]
          _ = e * (Q.1 * x) := by rw [hxq]
          _ = (e * Q.1) * x := by rw [mul_assoc]
      have hYc : pSpan (centMembers Ω (e * Q.1)) ≤ Subgroup.centralizer ({e * Q.1} : Set G) :=
        pSpan_le fun L hL => hL.2
      have hinv : ∀ L ∈ centMembers Ω (e * Q.1), ∀ x ∈ pSpan (centMembers Ω (e * Q.1)),
          conjSub x L ∈ centMembers Ω (e * Q.1) := by
        intro L hL x hx
        have hxc : x * (e * Q.1) = (e * Q.1) * x :=
          Subgroup.mem_centralizer_singleton_iff.mp (hYc hx)
        have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ.conjInvariant hL
          (n := x)
        rwa [show x * (e * Q.1) * x⁻¹ = e * Q.1 by rw [hxc, mul_inv_cancel_right]] at hc
      have hpN : p ∈ Subgroup.normalizer (R : Set G) :=
        (hbf.spec R hRΩ Q hRr ⟨p, hpD⟩).mp (by rw [hbf.symm]; exact hQ0)
      have hOm : M ∈ omegaStarNbr Ω R := by
        rcases h.mem_omegaStarNbr_or_twinSet h9 hRΩ hM hpM hpN with h8 | h8
        · exact h8
        · exfalso
          obtain ⟨-, z', hz'R, hz'M⟩ := h8
          exact hpr ((hpM.eq hz'M).trans (hRr.eq hz'R).symm)
      exact e16j_ae5_false h h9 (fun L hL => hL.1) hinv I ⟨hM, h2⟩ ⟨hRΩ, hRC⟩ hpM hRr hpr hOm


private theorem e16j_normalizer_iff_image {Ω P : Set (Subgroup G)} {n : ℕ} (hΩ : StarHyp Ω)
    (hP : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (I : AEIdent P n)
    {L : Subgroup G} (hL : L ∈ P) {x : G} (hx : x ∈ pSpan P) :
    x ∈ Subgroup.normalizer (L : Set G) ↔
      ∀ y ∈ Subgroup.map I.φ (L.subgroupOf (pSpan P)),
        I.φ ⟨x, hx⟩ * y * (I.φ ⟨x, hx⟩)⁻¹ ∈ Subgroup.map I.φ (L.subgroupOf (pSpan P)) := by
  constructor
  · intro hxN y hy
    obtain ⟨l, hl, rfl⟩ := hy
    have hlL : x * (l : G) * x⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hxN (l : G)).mp (Subgroup.mem_subgroupOf.mp hl)
    refine ⟨⟨x * (l : G) * x⁻¹, (pSpan P).mul_mem ((pSpan P).mul_mem hx l.2)
      ((pSpan P).inv_mem hx)⟩, Subgroup.mem_subgroupOf.mpr hlL, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  · intro hcond
    have hc : conjSub x L ∈ P := hinv L hL x hx
    have hmap : Subgroup.map I.φ ((conjSub x L).subgroupOf (pSpan P)) =
        Subgroup.map I.φ (L.subgroupOf (pSpan P)) := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        have ha' : x⁻¹ * (a : G) * x ∈ L := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp ha)
        have hlmem : I.φ ⟨x⁻¹ * (a : G) * x, (pSpan P).mul_mem ((pSpan P).mul_mem
            ((pSpan P).inv_mem hx) a.2) hx⟩ ∈ Subgroup.map I.φ (L.subgroupOf (pSpan P)) :=
          ⟨_, Subgroup.mem_subgroupOf.mpr ha', rfl⟩
        have hae : I.φ a = I.φ ⟨x, hx⟩ * I.φ ⟨x⁻¹ * (a : G) * x, (pSpan P).mul_mem
            ((pSpan P).mul_mem ((pSpan P).inv_mem hx) a.2) hx⟩ * (I.φ ⟨x, hx⟩)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          apply Subtype.ext
          simp [mul_assoc]
        rw [hae]
        exact hcond _ hlmem
      · intro w hw
        let g : Subgroup.map I.φ (L.subgroupOf (pSpan P)) →
            Subgroup.map I.φ (L.subgroupOf (pSpan P)) :=
          fun y => ⟨I.φ ⟨x, hx⟩ * (y : AE.AEQ n) * (I.φ ⟨x, hx⟩)⁻¹, hcond y y.2⟩
        have hginj : Function.Injective g := by
          intro a b hab
          apply Subtype.ext
          have h1 := congrArg Subtype.val hab
          exact mul_left_cancel (mul_right_cancel h1)
        obtain ⟨y, hy⟩ := Finite.surjective_of_injective hginj ⟨w, hw⟩
        obtain ⟨l, hl, hly⟩ := y.2
        have hyw : I.φ ⟨x, hx⟩ * (y : AE.AEQ n) * (I.φ ⟨x, hx⟩)⁻¹ = w :=
          congrArg Subtype.val hy
        refine ⟨⟨x * (l : G) * x⁻¹, (pSpan P).mul_mem ((pSpan P).mul_mem hx l.2)
          ((pSpan P).inv_mem hx)⟩, ?_, ?_⟩
        · apply Subgroup.mem_subgroupOf.mpr
          apply mem_conjSub_iff.mpr
          have e1 : x⁻¹ * (x * (l : G) * x⁻¹) * x = (l : G) := by group
          rw [e1]
          exact Subgroup.mem_subgroupOf.mp hl
        · have hae : I.φ ⟨x * (l : G) * x⁻¹, (pSpan P).mul_mem ((pSpan P).mul_mem hx l.2)
              ((pSpan P).inv_mem hx)⟩ = I.φ ⟨x, hx⟩ * I.φ l * (I.φ ⟨x, hx⟩)⁻¹ := by
            rw [← map_inv, ← map_mul, ← map_mul]
            congr 1
          rw [hae, hly, hyw]
    have heq := StarHyp.aeIdent_map_injective hΩ hP I hc hL hmap
    exact mem_normalizer_iff_conjSub_eq.mpr heq

private theorem e16j_mem_normalizer_of_le {R : Subgroup G} {x : G}
    (hRC : R ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : ∀ r ∈ R, x * r = r * x := fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)).symm
  constructor
  · intro hy
    have e1 : x * y * x⁻¹ = y := by rw [hc y hy, mul_inv_cancel_right]
    rw [e1]
    exact hy
  · intro hy
    have e1 : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
      calc x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [hc _ hy]
        _ = x * y * x⁻¹ := by group
    have e2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [e2, e1]
    exact hy

theorem e16j_mem_sigma_iff [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω)
    {R : Subgroup G} (hR : R ∈ Ω) {p : zGroup Ω} (hp : IsUniqueInvolution R p.1) :
    p ∈ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩ ↔ R ≤ Subgroup.centralizer ({e} : Set G) := by
  have hpS : p ∈ zPoints Ω := ⟨R, hR, hp⟩
  constructor
  · intro hps
    have hb : bf ⟨e, heD⟩ p = 0 := hps.2
    have heN : e ∈ Subgroup.normalizer (R : Set G) := (hbf.spec R hR p hp ⟨e, heD⟩).mp hb
    exact le_centralizer_of_mem_normalizer c hh.out hh9.out h13 hR heN
  · intro hRC
    exact ⟨hpS, (hbf.spec R hR p hp ⟨e, heD⟩).mpr (e16j_mem_normalizer_of_le hRC)⟩

private theorem e16j_psi_inv {P : Set (Subgroup G)} (I : AEIdent P 6)
    (ψ : ↥(pSpan P) ≃* ↥(AE.aeSub 6))
    (hψ : ∀ L ∈ P, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      Subgroup.map I.φ (L.subgroupOf (pSpan P)) = AE.memBar α hα b →
        Subgroup.map (AE.aeSub 6).subtype
          (Subgroup.map ψ.toMonoidHom (L.subgroupOf (pSpan P))) = AE.memAt α hα b)
    {L : Subgroup G} (hL : L ∈ P) {α : Finset (Fin 6)} {hα : α.card = 4} {b : Bool}
    (hlab : Subgroup.map I.φ (L.subgroupOf (pSpan P)) = AE.memBar α hα b)
    {r : G} (hr : IsUniqueInvolution L r) (hrX : r ∈ pSpan P) :
    (ψ ⟨r, hrX⟩ : AE.Wr 6) = AE.zOf (AE.emb α hα) := by
  have hmem : (ψ ⟨r, hrX⟩ : AE.Wr 6) ∈ AE.memAt α hα b := by
    rw [← hψ L hL α hα b hlab]
    exact ⟨ψ ⟨r, hrX⟩, ⟨⟨r, hrX⟩, Subgroup.mem_subgroupOf.mpr hr.mem, rfl⟩, rfl⟩
  have hsq : (ψ ⟨r, hrX⟩ : AE.Wr 6) * (ψ ⟨r, hrX⟩ : AE.Wr 6) = 1 := by
    have h1 : ψ ⟨r, hrX⟩ * ψ ⟨r, hrX⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨r, hrX⟩ : ↥(pSpan P)) * ⟨r, hrX⟩ = 1 := by
        apply Subtype.ext
        exact hr.sq
      rw [h2, map_one]
    exact congrArg Subtype.val h1
  rcases AE.eq_of_mem_memAt_mul_self hmem hsq with h1 | h1
  · exfalso
    have h2 : ψ ⟨r, hrX⟩ = 1 := Subtype.ext h1
    have h3 : (⟨r, hrX⟩ : ↥(pSpan P)) = 1 := ψ.injective (by rw [h2, map_one])
    exact hr.ne_one (congrArg Subtype.val h3)
  · exact h1

private theorem e16j_orth (h : EndHyp Ω) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) (I : AEIdent P 6) {L L' : Subgroup G}
    (hL : L ∈ P) (hL' : L' ∈ P) {α β : Finset (Fin 6)} {hα : α.card = 4} {hβ : β.card = 4}
    {b b' : Bool} (hlab : Subgroup.map I.φ (L.subgroupOf (pSpan P)) = AE.memBar α hα b)
    (hlab' : Subgroup.map I.φ (L'.subgroupOf (pSpan P)) = AE.memBar β hβ b')
    {p q : zGroup Ω} (hp : IsUniqueInvolution L p.1) (hq : IsUniqueInvolution L' q.1) :
    bf q p = 0 ↔ ((α.filter (· ∈ β)).card : ZMod 2) = 0 := by
  have hsp : q.1 ∈ pSpan P := le_pSpan hL' hq.mem
  rw [hbf.spec L (hPΩ hL) p hp q, e16j_normalizer_iff_image h.toStarHyp hPΩ hinv I hL hsp]
  rw [TC.Thin.phi_map_eq_zBar I.φ (by norm_num) hL' (h.card_eq_eight (hPΩ hL')) hlab' hq, hlab]
  rw [TC.Thin.zBar_eq_vbar_indv β hβ]
  unfold TL4.vbar
  rw [AE.vec_normalizes_memBar_iff (by norm_num) α hα b (TC.Thin.indv β)]
  unfold TC.Thin.indv
  rw [Finset.sum_boole]

private theorem e16j_hinv_centMembers {a : G} (hΩ : ConjInvariant Ω) :
    ∀ L ∈ centMembers Ω a, ∀ x ∈ pSpan (centMembers Ω a), conjSub x L ∈ centMembers Ω a := by
  intro L hL x hx
  have hY : pSpan (centMembers Ω a) ≤ Subgroup.centralizer ({a} : Set G) :=
    pSpan_le fun L' hL' => hL'.2
  have hxc : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hY hx)
  have hc := CFSG.ClassicalInvolution.Generic.conjSub_mem_centMembers hΩ hL (n := x)
  rwa [show x * a * x⁻¹ = a by rw [hxc, mul_inv_cancel_right]] at hc

private theorem e16j_param [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω)
    (I : AEIdent (centMembers Ω e) 6) (ψ : ↥(pSpan (centMembers Ω e)) ≃* ↥(AE.aeSub 6))
    (hψ : ∀ L ∈ centMembers Ω e, ∀ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool),
      Subgroup.map I.φ (L.subgroupOf (pSpan (centMembers Ω e))) = AE.memBar α hα b →
        Subgroup.map (AE.aeSub 6).subtype
          (Subgroup.map ψ.toMonoidHom (L.subgroupOf (pSpan (centMembers Ω e)))) = AE.memAt α hα b) :
    ∃ (L : {α : Finset (Fin 6) // α.card = 4} → Subgroup G)
      (Pt : {α : Finset (Fin 6) // α.card = 4} → zGroup Ω),
      (∀ α, L α ∈ centMembers Ω e) ∧
      (∀ α, Subgroup.map I.φ ((L α).subgroupOf (pSpan (centMembers Ω e))) =
        AE.memBar α.1 α.2 true) ∧
      (∀ α, IsUniqueInvolution (L α) (Pt α).1) ∧ Function.Injective Pt ∧
      Polar.sigma bf (zPoints Ω) ⟨e, heD⟩ = Set.range Pt := by
  have hΩ : HypOmegaGen Ω := hh.out.thmD.hyp
  have hPΩ : centMembers Ω e ⊆ Ω := fun L hL => hL.1
  have hlab : ∀ α : {α : Finset (Fin 6) // α.card = 4}, ∃ L ∈ centMembers Ω e,
      Subgroup.map I.φ (L.subgroupOf (pSpan (centMembers Ω e))) = AE.memBar α.1 α.2 true :=
    fun α => I.label_surj α.1 α.2 true
  choose L hLP hLlab using hlab
  have hrL : ∀ α, ∃ r : G, IsUniqueInvolution (L α) r := fun α =>
    (hΩ.omega1 (L α) (hPΩ (hLP α))).1
  choose r hr using hrL
  have hrX : ∀ α, r α ∈ pSpan (centMembers Ω e) := fun α => le_pSpan (hLP α) (hr α).mem
  have hrD : ∀ α, r α ∈ zGroup Ω := fun α => Subgroup.subset_closure ⟨L α, hPΩ (hLP α), hr α⟩
  let Pt : {α : Finset (Fin 6) // α.card = 4} → zGroup Ω := fun α => ⟨r α, hrD α⟩
  have hψPt : ∀ α, (ψ ⟨r α, hrX α⟩ : AE.Wr 6) = AE.zOf (AE.emb α.1 α.2) := fun α =>
    e16j_psi_inv I ψ hψ (hLP α) (hLlab α) (hr α) (hrX α)
  have hPtinj : Function.Injective Pt := by
    intro α β hab
    have hrab : r α = r β := congrArg Subtype.val hab
    have hz : AE.zBar α.1 α.2 = AE.zBar β.1 β.2 := by
      have hsub : (⟨r α, hrX α⟩ : ↥(pSpan (centMembers Ω e))) = ⟨r β, hrX β⟩ :=
        Subtype.ext hrab
      have h1 : (ψ ⟨r α, hrX α⟩ : AE.Wr 6) = (ψ ⟨r β, hrX β⟩ : AE.Wr 6) := by rw [hsub]
      rw [hψPt α, hψPt β] at h1
      show AE.mkQ 6 (AE.zOf (AE.emb α.1 α.2)) = AE.mkQ 6 (AE.zOf (AE.emb β.1 β.2))
      rw [h1]
    exact Subtype.ext (AE.eq_of_zBar_eq (by norm_num) hz)
  have hsig : Polar.sigma bf (zPoints Ω) ⟨e, heD⟩ = Set.range Pt := by
    ext p
    constructor
    · rintro ⟨hpS, hb⟩
      obtain ⟨R, hRΩ, hR⟩ := hpS
      have hRC : R ≤ Subgroup.centralizer ({e} : Set G) :=
        (e16j_mem_sigma_iff c h13 hbf heD hRΩ hR).mp ⟨⟨R, hRΩ, hR⟩, hb⟩
      have hRP : R ∈ centMembers Ω e := ⟨hRΩ, hRC⟩
      obtain ⟨α, hα, b, hlabR⟩ := I.label R hRP
      have hpX : p.1 ∈ pSpan (centMembers Ω e) := le_pSpan hRP hR.mem
      have h1 : (ψ ⟨p.1, hpX⟩ : AE.Wr 6) = (ψ ⟨r ⟨α, hα⟩, hrX ⟨α, hα⟩⟩ : AE.Wr 6) := by
        rw [e16j_psi_inv I ψ hψ hRP hlabR hR hpX, hψPt ⟨α, hα⟩]
      have h2 : (⟨p.1, hpX⟩ : ↥(pSpan (centMembers Ω e))) = ⟨r ⟨α, hα⟩, hrX ⟨α, hα⟩⟩ :=
        ψ.injective (Subtype.ext h1)
      exact ⟨⟨α, hα⟩, Subtype.ext (congrArg Subtype.val h2).symm⟩
    · rintro ⟨α, rfl⟩
      exact (e16j_mem_sigma_iff c h13 hbf heD (hPΩ (hLP α)) (hr α)).mpr (hLP α).2
  exact ⟨L, Pt, hLP, hLlab, fun α => hr α, hPtinj, hsig⟩

theorem e16j_card_sigma [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω) :
    (Polar.sigma bf (zPoints Ω) ⟨e, heD⟩).ncard = 15 := by
  obtain ⟨I, ψ, -, -, hψ, -, -⟩ := c.exists_equiv_X hh.out hh9.out h13
  obtain ⟨-, Pt, -, -, -, hinj, hsig⟩ := e16j_param c h13 hbf heD I ψ hψ
  rw [hsig, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
    Nat.card_eq_fintype_card]
  decide

private theorem e16j_inter_card : ∀ α β : {α : Finset (Fin 6) // α.card = 4}, α ≠ β →
    (α.1 ∩ β.1).card = 2 ∨ (α.1 ∩ β.1).card = 3 := by decide

theorem e16j_card_nbr [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω)
    {p : zGroup Ω} (hp : p ∈ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩) :
    (Polar.nbr bf (zPoints Ω) p ∩ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩).ncard = 6 := by
  obtain ⟨I, ψ, -, -, hψ, -, -⟩ := c.exists_equiv_X hh.out hh9.out h13
  obtain ⟨L, Pt, hLP, hLlab, hLr, hinj, hsig⟩ := e16j_param c h13 hbf heD I ψ hψ
  have hΩ : HypOmegaGen Ω := hh.out.thmD.hyp
  have hPΩ : centMembers Ω e ⊆ Ω := fun L hL => hL.1
  rw [hsig] at hp ⊢
  obtain ⟨α, rfl⟩ := hp
  have hinv := e16j_hinv_centMembers (a := e) hΩ.conjInvariant
  have hset : Polar.nbr bf (zPoints Ω) (Pt α) ∩ Set.range Pt =
      Pt '' {β : {α : Finset (Fin 6) // α.card = 4} | (α.1 ∩ β.1).card = 2} := by
    ext q
    constructor
    · rintro ⟨⟨hqS, hqne, hb⟩, β, rfl⟩
      have hβα : β ≠ α := fun e' => hqne (congrArg Pt e')
      have hb' : bf (Pt β) (Pt α) = 0 := by rw [hbf.symm]; exact hb
      have hpar := e16j_orth hh.out hbf hPΩ hinv I (hLP α) (hLP β) (hLlab α) (hLlab β)
        (hLr α) (hLr β) |>.mp hb'
      rw [Finset.filter_mem_eq_inter] at hpar
      rcases e16j_inter_card α β (fun e' => hβα e'.symm) with h2 | h2
      · exact ⟨β, h2, rfl⟩
      · rw [h2] at hpar
        exact absurd hpar (by decide)
    · rintro ⟨β, hβ, rfl⟩
      have hβα : β ≠ α := by
        intro e'
        have hβ' : (α.1 ∩ β.1).card = 2 := hβ
        have h4 := α.2
        rw [e', Finset.inter_self] at hβ'
        omega
      refine ⟨⟨⟨L β, hPΩ (hLP β), hLr β⟩, fun e' => hβα (hinj e'), ?_⟩, β, rfl⟩
      rw [hbf.symm]
      apply (e16j_orth hh.out hbf hPΩ hinv I (hLP α) (hLP β) (hLlab α) (hLlab β)
        (hLr α) (hLr β)).mpr
      rw [Finset.filter_mem_eq_inter, hβ]
      decide
  have hcount : ∀ α : {α : Finset (Fin 6) // α.card = 4},
      (Finset.univ.filter fun β : {α : Finset (Fin 6) // α.card = 4} =>
        (α.1 ∩ β.1).card = 2).card = 6 := by decide
  rw [hset, Set.ncard_image_of_injective _ hinj]
  have hS : {β : {α : Finset (Fin 6) // α.card = 4} | (α.1 ∩ β.1).card = 2} =
      ↑(Finset.univ.filter fun β : {α : Finset (Fin 6) // α.card = 4} =>
        (α.1 ∩ β.1).card = 2) := by
    ext β
    simp
  rw [hS, Set.ncard_coe_finset]
  exact hcount α

private theorem e16j_zOf_mul {α β γ : Finset (Fin 6)} (hα : α.card = 4) (hβ : β.card = 4)
    (hγ : γ.card = 4) (h : γ = _root_.symmDiff α β) :
    AE.zOf (AE.emb α hα) * AE.zOf (AE.emb β hβ) = AE.zOf (AE.emb γ hγ) := by
  refine AE.Wr.ext (funext fun x => ?_) ?_
  · have hmem : ∀ (δ : Finset (Fin 6)) (hδ : δ.card = 4) (y : Fin 6),
        y ∈ Set.range (AE.emb δ hδ) ↔ y ∈ δ := fun δ hδ y => by
      rw [AE.range_emb]
      exact Finset.mem_coe
    have hsym : ∀ y : Fin 6, (Equiv.symm (1 : Equiv.Perm (Fin 6))) y = y := fun y => rfl
    simp only [AE.Wr.mul_vec, AE.zOf_perm, AE.zOf_vec_apply, hmem, hsym, h, Finset.mem_symmDiff]
    by_cases hxa : x ∈ α <;> by_cases hxb : x ∈ β <;> simp [hxa, hxb] <;> decide
  · rw [AE.Wr.mul_perm, AE.zOf_perm, AE.zOf_perm, AE.zOf_perm, mul_one]

private theorem e16j_noplane_comb : ∀ α β γ : {α : Finset (Fin 6) // α.card = 4},
    (α.1 ∩ β.1).card = 2 → (α.1 ∩ γ.1).card = 2 → β.1 ≠ γ.1 →
      γ.1 ≠ _root_.symmDiff α.1 β.1 → (β.1 ∩ γ.1).card = 3 := by
  decide

private theorem e16j_mem_nbr_iff (h : EndHyp Ω) {bf : zGroup Ω → zGroup Ω → ZMod 2}
    (hbf : IsEndForm Ω bf) (I : AEIdent (centMembers Ω e) 6)
    {L : {α : Finset (Fin 6) // α.card = 4} → Subgroup G}
    {Pt : {α : Finset (Fin 6) // α.card = 4} → zGroup Ω}
    (hLP : ∀ α, L α ∈ centMembers Ω e)
    (hLlab : ∀ α, Subgroup.map I.φ ((L α).subgroupOf (pSpan (centMembers Ω e))) =
      AE.memBar α.1 α.2 true)
    (hLr : ∀ α, IsUniqueInvolution (L α) (Pt α).1)
    (hinj : Function.Injective Pt) (α β : {α : Finset (Fin 6) // α.card = 4}) :
    Pt β ∈ Polar.nbr bf (zPoints Ω) (Pt α) ↔ (α.1 ∩ β.1).card = 2 := by
  have hPΩ : centMembers Ω e ⊆ Ω := fun L hL => hL.1
  have hinv := e16j_hinv_centMembers (a := e) h.thmD.hyp.conjInvariant
  constructor
  · rintro ⟨hqS, hqne, hb⟩
    have hβα : β ≠ α := fun e' => hqne (congrArg Pt e')
    have hb' : bf (Pt β) (Pt α) = 0 := by rw [hbf.symm]; exact hb
    have hpar := (e16j_orth h hbf hPΩ hinv I (hLP α) (hLP β) (hLlab α) (hLlab β)
      (hLr α) (hLr β)).mp hb'
    rw [Finset.filter_mem_eq_inter] at hpar
    rcases e16j_inter_card α β (fun e' => hβα e'.symm) with h2 | h2
    · exact h2
    · rw [h2] at hpar
      exact absurd hpar (by decide)
  · intro h2
    have hβα : β ≠ α := by
      intro e'
      have hβ' : (α.1 ∩ β.1).card = 2 := h2
      have h4 := α.2
      rw [e', Finset.inter_self] at hβ'
      omega
    refine ⟨⟨L β, hPΩ (hLP β), hLr β⟩, fun e' => hβα (hinj e'), ?_⟩
    rw [hbf.symm]
    apply (e16j_orth h hbf hPΩ hinv I (hLP α) (hLP β) (hLlab α) (hLlab β)
      (hLr α) (hLr β)).mpr
    rw [Finset.filter_mem_eq_inter, h2]
    decide

theorem e16j_noplane [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω)
    {p : zGroup Ω} (hp : p ∈ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩)
    {x : zGroup Ω} (hx : x ∈ Polar.nbr bf (zPoints Ω) p ∩ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩)
    {y : zGroup Ω} (hy : y ∈ Polar.nbr bf (zPoints Ω) p ∩ Polar.sigma bf (zPoints Ω) ⟨e, heD⟩)
    (hyx : y ≠ x) (hyp : y ≠ p * x) : bf x y = 1 := by
  obtain ⟨I, ψ, -, -, hψ, -, -⟩ := c.exists_equiv_X hh.out hh9.out h13
  obtain ⟨L, Pt, hLP, hLlab, hLr, hinj, hsig⟩ := e16j_param c h13 hbf heD I ψ hψ
  have hPΩ : centMembers Ω e ⊆ Ω := fun L hL => hL.1
  have hinv := e16j_hinv_centMembers (a := e) hh.out.thmD.hyp.conjInvariant
  rw [hsig] at hp hx hy
  obtain ⟨α, rfl⟩ := hp
  obtain ⟨hxn, β, rfl⟩ := hx
  obtain ⟨hyn, γ, rfl⟩ := hy
  have hβ := (e16j_mem_nbr_iff hh.out hbf I hLP hLlab hLr hinj α β).mp hxn
  have hγ := (e16j_mem_nbr_iff hh.out hbf I hLP hLlab hLr hinj α γ).mp hyn
  have hβγ : β.1 ≠ γ.1 := fun e' => hyx (congrArg Pt (Subtype.ext e'.symm))
  have hX : ∀ δ, (Pt δ).1 ∈ pSpan (centMembers Ω e) := fun δ => le_pSpan (hLP δ) (hLr δ).mem
  have hψP : ∀ δ, (ψ ⟨(Pt δ).1, hX δ⟩ : AE.Wr 6) = AE.zOf (AE.emb δ.1 δ.2) := fun δ =>
    e16j_psi_inv I ψ hψ (hLP δ) (hLlab δ) (hLr δ) (hX δ)
  have hXmul : (Pt α * Pt β).1 ∈ pSpan (centMembers Ω e) :=
    (pSpan (centMembers Ω e)).mul_mem (hX α) (hX β)
  have hne : γ.1 ≠ _root_.symmDiff α.1 β.1 := by
    intro he
    apply hyp
    have hprod : (ψ ⟨(Pt α * Pt β).1, hXmul⟩ : AE.Wr 6) = AE.zOf (AE.emb γ.1 γ.2) := by
      have hsplit : (⟨(Pt α * Pt β).1, hXmul⟩ : ↥(pSpan (centMembers Ω e))) =
          ⟨(Pt α).1, hX α⟩ * ⟨(Pt β).1, hX β⟩ := rfl
      rw [hsplit, map_mul, Subgroup.coe_mul, hψP α, hψP β]
      exact e16j_zOf_mul α.2 β.2 γ.2 he
    have hsub : (⟨(Pt γ).1, hX γ⟩ : ↥(pSpan (centMembers Ω e))) =
        ⟨(Pt α * Pt β).1, hXmul⟩ :=
      ψ.injective (Subtype.ext (by rw [hψP γ, hprod]))
    have hG := congrArg Subtype.val hsub
    exact Subtype.ext hG
  have hcomb := e16j_noplane_comb α β γ hβ hγ hβγ hne
  have hiff := e16j_orth hh.out hbf hPΩ hinv I (hLP γ) (hLP β) (hLlab γ) (hLlab β)
    (hLr γ) (hLr β)
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm, hcomb] at hiff
  have hne0 : bf (Pt β) (Pt γ) ≠ 0 := fun h0 => absurd (hiff.mp h0) (by decide)
  have hZ2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
  exact hZ2 _ hne0

theorem e16j_unique [hh : Fact (EndHyp Ω)] [hh9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) (heD : e ∈ zGroup Ω)
    {p x : zGroup Ω} (hp : p ∈ zPoints Ω) (hx : x ∈ Polar.nbr bf (zPoints Ω) p) :
    ∃! E : zGroup Ω, (∃ y : G, E.1 = y * e * y⁻¹) ∧ p ∈ Polar.sigma bf (zPoints Ω) E ∧
      x ∈ Polar.sigma bf (zPoints Ω) E := by
  have h : EndHyp Ω := hh.out
  have h9 : Perp9 Ω := hh9.out
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  obtain ⟨Mp, hMpΩ, hMp⟩ := hp
  obtain ⟨hxS, hxne, hb⟩ := hx
  obtain ⟨Mx, hMxΩ, hMx⟩ := hxS
  have hpN : p.1 ∈ Subgroup.normalizer (Mx : Set G) := (hbf.spec Mx hMxΩ x hMx p).mp hb
  have hMpOm : Mp ∈ omegaStarNbr Ω Mx := by
    rcases h.mem_omegaStarNbr_or_twinSet h9 hMxΩ hMpΩ hMp hpN with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨-, z', hz'x, hz'p⟩ := h1
      exact hxne (Subtype.ext (((hMp.eq hz'p).trans (hMx.eq hz'x).symm).symm))
  have hMxOm : Mx ∈ omegaStarNbr Ω Mp := Q3T6.Mu.omegaStarNbr_symm hΩ hMxΩ hMpΩ hMpOm
  obtain ⟨n, hn⟩ := h.thmD.trans K c.twin.mem Mp hMpΩ
  subst hn
  have hMxOmn : Mx ∈ omegaStarNbr Ω (conjSub n K) := hMxOm
  obtain ⟨W₁, u₁, e₁, g₁, c₁, hMxD, y₀, hy₀⟩ :=
    exists_frame_of_omegaStarNbr (c.conjG h n) h h9 hMxOmn
  have hz₁ : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := (c.conjG h n).twin.isInv
  have hpz : p.1 = n * z * n⁻¹ := hMp.eq hz₁
  have hsq : n * z * n⁻¹ * (n * z * n⁻¹) = 1 := hz₁.sq
  have h13₁ : zGroup Ω ≠ eGroup Ω (conjSub n K) := h.zGroup_ne_eGroup_conj c.twin.mem h13 n
  have he₁D : e₁ ∈ zGroup Ω := (u_mem_zGroup c₁ h h9 h13₁).2
  have hpW : p.1 ∈ W₁ := by rw [hpz]; exact c₁.data.hzW
  have hMpD : conjSub n K ∈ DSet Ω W₁ := h.mem_dSet_of_mem c₁.data.hW hMpΩ hMp hpW
  have hpx : (p * x).1 = n * z * n⁻¹ * x.1 := by
    show p.1 * x.1 = _
    rw [hpz]
  have hE₁ : ∃ y : G, e₁ = y * e * y⁻¹ := ⟨y₀ * n, by rw [hy₀]; group⟩
  refine ⟨⟨e₁, he₁D⟩, ⟨hE₁, ?_, ?_⟩, ?_⟩
  · exact (e16j_mem_sigma_iff c₁ h13₁ hbf he₁D hMpΩ hMp).mpr (c₁.dSet_le_centralizer _ hMpD)
  · exact (e16j_mem_sigma_iff c₁ h13₁ hbf he₁D hMxΩ hMx).mpr
      (c₁.dSet_le_centralizer _ hMxD)
  · rintro E' ⟨⟨y', hy'⟩, hpE', hxE'⟩
    have hE'D : y' * e * y'⁻¹ ∈ zGroup Ω := by rw [← hy']; exact E'.2
    have hE'eq : E' = ⟨y' * e * y'⁻¹, hE'D⟩ := Subtype.ext hy'
    subst hE'eq
    have h13' : zGroup Ω ≠ eGroup Ω (conjSub y' K) := h.zGroup_ne_eGroup_conj c.twin.mem h13 y'
    have hkey : ∀ q : zGroup Ω, (q = p ∨ q = x ∨ q = p * x) →
        bf ⟨y' * e * y'⁻¹, hE'D⟩ q = 0 := by
      rintro q (rfl | rfl | rfl)
      · exact hpE'.2
      · exact hxE'.2
      · rw [hbf.mul_right, hpE'.2, hxE'.2, add_zero]
    have hD : DSet Ω W₁ ⊆ centMembers Ω (y' * e * y'⁻¹) := by
      intro R hR
      have hRΩ : R ∈ Ω := ((h.mem_dSet_iff).mp hR).1
      obtain ⟨r, hr⟩ := (hΩ.omega1 R hRΩ).1
      have hrZ : r ∈ zGroup Ω := Subgroup.subset_closure ⟨R, hRΩ, hr⟩
      have hR1 := c₁.zValues h h9 R hR r hr
      have hxZ := c₁.zValues h h9 Mx hMxD x.1 hMx
      have hQ : bf ⟨y' * e * y'⁻¹, hE'D⟩ ⟨r, hrZ⟩ = 0 := by
        rcases hxZ with hx1 | hx1 | hx1
        · exact absurd (Subtype.ext (hx1.trans hpz.symm)) hxne
        · rcases hR1 with hr1 | hr1 | hr1
          · refine hkey _ (Or.inl (Subtype.ext ?_))
            show r = p.1
            rw [hr1, hpz]
          · refine hkey _ (Or.inr (Or.inl (Subtype.ext ?_)))
            show r = x.1
            rw [hr1, hx1]
          · refine hkey _ (Or.inr (Or.inr (Subtype.ext ?_)))
            show r = (p * x).1
            rw [hr1, hpx, hx1]
        · rcases hR1 with hr1 | hr1 | hr1
          · refine hkey _ (Or.inl (Subtype.ext ?_))
            show r = p.1
            rw [hr1, hpz]
          · refine hkey _ (Or.inr (Or.inr (Subtype.ext ?_)))
            show r = (p * x).1
            rw [hr1, hpx, hx1, ← mul_assoc, hsq, one_mul]
          · refine hkey _ (Or.inr (Or.inl (Subtype.ext ?_)))
            show r = x.1
            rw [hr1, hx1]
      have hpt : (⟨r, hrZ⟩ : zGroup Ω) ∈ zPoints Ω := ⟨R, hRΩ, hr⟩
      exact ⟨hRΩ, (e16j_mem_sigma_iff (c.conjG h y') h13' hbf hE'D hRΩ hr).mp ⟨hpt, hQ⟩⟩
    have hH2 := Sit16.eq_of_dSet_subset_centMembers (c.conjG h y') c₁ h h9 h13' hD
    exact Subtype.ext hH2.symm

theorem sections_of_frame [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    Polar.Sections bf (zPoints Ω) {x : zGroup Ω | ∃ y : G, x.1 = y * e * y⁻¹} := by
  have h : EndHyp Ω := hh.out
  have heD : e ∈ zGroup Ω := (u_mem_zGroup c h h9.out h13).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro E ⟨y, hy⟩ hE1
    apply c.data.he1
    have hy1 : y * e * y⁻¹ = 1 := by rw [← hy, hE1]; rfl
    calc e = y⁻¹ * (y * e * y⁻¹) * y := by group
      _ = 1 := by rw [hy1]; group
  · rintro E ⟨y, hy⟩
    have heD' : y * e * y⁻¹ ∈ zGroup Ω := by rw [← hy]; exact E.2
    have hEeq : E = ⟨y * e * y⁻¹, heD'⟩ := Subtype.ext hy
    subst hEeq
    exact e16j_card_sigma (c.conjG h y) (h.zGroup_ne_eGroup_conj c.twin.mem h13 y) hbf heD'
  · rintro E ⟨y, hy⟩ p hp
    have heD' : y * e * y⁻¹ ∈ zGroup Ω := by rw [← hy]; exact E.2
    have hEeq : E = ⟨y * e * y⁻¹, heD'⟩ := Subtype.ext hy
    subst hEeq
    exact e16j_card_nbr (c.conjG h y) (h.zGroup_ne_eGroup_conj c.twin.mem h13 y) hbf heD' hp
  · rintro E ⟨y, hy⟩ p hp x hx w hw hwx hwp
    have heD' : y * e * y⁻¹ ∈ zGroup Ω := by rw [← hy]; exact E.2
    have hEeq : E = ⟨y * e * y⁻¹, heD'⟩ := Subtype.ext hy
    subst hEeq
    exact e16j_noplane (c.conjG h y) (h.zGroup_ne_eGroup_conj c.twin.mem h13 y) hbf heD' hp hx
      hw hwx hwp
  · intro p hp x hx
    exact e16j_unique c h13 hbf heD hp hx

theorem exists_two_sections [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    ∃ p ∈ zPoints Ω, ∃ x₁ x₂ : zGroup Ω, (∃ y : G, x₁.1 = y * e * y⁻¹) ∧
      (∃ y : G, x₂.1 = y * e * y⁻¹) ∧ x₁ ≠ x₂ ∧ p ∈ Polar.sigma bf (zPoints Ω) x₁ ∧
        p ∈ Polar.sigma bf (zPoints Ω) x₂ := by
  have h : EndHyp Ω := hh.out
  have h9' : Perp9 Ω := h9.out
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩ.conjInvariant
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have heD : e ∈ zGroup Ω := (u_mem_zGroup c h h9' h13).2
  have heN : e ∈ Subgroup.normalizer (K : Set G) := by
    have he := e_mem_lambdaW c h h9' h13
    rw [lambdaW_eq c h h9' h13] at he
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp he).1).2
  obtain ⟨e', he', hne⟩ := Set.exists_ne_of_one_lt_ncard
    (lt_of_lt_of_le one_lt_two (c.two_le_ncard_centres h h9' h13)) e
  obtain ⟨n, hnN, hn⟩ := c.exists_mem_normalizer_conj_centre h h9' he'
  have he'D : e' ∈ zGroup Ω := by
    have hc := hDN.conj_mem e heD n
    rwa [hn] at hc
  have he'N : e' ∈ Subgroup.normalizer (K : Set G) := by
    rw [← hn]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN heN) (Subgroup.inv_mem _ hnN)
  have hzP : (⟨z, hzD⟩ : zGroup Ω) ∈ zPoints Ω := ⟨K, c.twin.mem, c.twin.isInv⟩
  refine ⟨⟨z, hzD⟩, hzP, ⟨e, heD⟩, ⟨e', he'D⟩, ⟨1, by simp⟩, ⟨n, hn.symm⟩, ?_, ?_, ?_⟩
  · exact fun heq => hne (congrArg Subtype.val heq).symm
  · exact ⟨hzP, (hbf.spec K c.twin.mem ⟨z, hzD⟩ c.twin.isInv ⟨e, heD⟩).mpr heN⟩
  · exact ⟨hzP, (hbf.spec K c.twin.mem ⟨z, hzD⟩ c.twin.isInv ⟨e', he'D⟩).mpr he'N⟩

private theorem e16j_pointSet_nine [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) :
    Polar.PointSet bf (zPoints Ω) 9 ∧
      Polar.Sections bf (zPoints Ω) {x : zGroup Ω | ∃ y : G, x.1 = y * e * y⁻¹} ∧
        Nat.card (zGroup Ω) = 64 := by
  obtain ⟨a, hPS⟩ := EndHyp.exists_pointSet c.twin h13 hbf
  have hSec := sections_of_frame c h13 hbf
  have hcard : Nat.card (zGroup Ω) = 64 :=
    (natCard_zGroup_eq_sixtyFour_of_frame c hh.out h9.out h13).1
  obtain ⟨q, hq, x₁, x₂, ⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hne, h1, h2⟩ := exists_two_sections c h13 hbf
  have ha : a = 9 := Polar.Sections.card_nbr_eq hbf.sympForm hPS hSec hcard
    ⟨q, hq, x₁, ⟨y₁, hy₁⟩, x₂, ⟨y₂, hy₂⟩, hne, h1, h2⟩
  subst ha
  exact ⟨hPS, hSec, hcard⟩

theorem card_nbr_eq_eighteen [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) {p : zGroup Ω} (hp : p ∈ zPoints Ω) :
    (Polar.nbr bf (zPoints Ω) p).ncard = 18 := by
  obtain ⟨hPS, -, -⟩ := e16j_pointSet_nine c h13 hbf
  have := Polar.PointSet.card_nbr hPS p hp
  omega

theorem card_zPoints_eq [hh : Fact (EndHyp Ω)] [h9 : Fact (Perp9 Ω)]
    (c : Sit16 Ω K K' W z u e g) (h13 : zGroup Ω ≠ eGroup Ω K)
    {bf : zGroup Ω → zGroup Ω → ZMod 2} (hbf : IsEndForm Ω bf) : (zPoints Ω).ncard = 35 := by
  obtain ⟨hPS, hSec, hcard⟩ := e16j_pointSet_nine c h13 hbf
  obtain ⟨q, hq, x₁, x₂, ⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hne, h1, h2⟩ := exists_two_sections c h13 hbf
  exact Polar.Sections.card_points_eq hbf.sympForm hPS hSec hcard
    ⟨q, hq, x₁, ⟨y₁, hy₁⟩, x₂, ⟨y₂, hy₂⟩, hne, h1, h2⟩

theorem inf_normalizer_eq_eGroup (c : Sit16 Ω K K' W z u e g)
    (h : EndHyp Ω) (h9 : Perp9 Ω) (h13 : zGroup Ω ≠ eGroup Ω K) :
    zGroup Ω ⊓ Subgroup.normalizer (K : Set G) = eGroup Ω K ∧
      Nat.card (zGroup Ω) = 2 * Nat.card (eGroup Ω K) := by
  haveI : Fact (EndHyp Ω) := ⟨h⟩
  haveI : Fact (Perp9 Ω) := ⟨h9⟩
  obtain ⟨bf, hbf⟩ := h.exists_endForm h9 c.twin h13
  obtain ⟨hPS, hSec, hcard⟩ := e16j_pointSet_nine c h13 hbf
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, c.twin.mem, c.twin.isInv⟩
  have hpP : (⟨z, hzD⟩ : zGroup Ω) ∈ zPoints Ω := ⟨K, c.twin.mem, c.twin.isInv⟩
  have hED : eGroup Ω K ≤ zGroup Ω := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨J, hJ, hx⟩
    have hJΩ : J ∈ Ω := by
      rcases hJ with rfl | hJ
      · exact c.twin.mem
      · exact hJ.1
    exact Subgroup.subset_closure ⟨J, hJΩ, hx⟩
  have hN : ∀ x : zGroup Ω, x.1 ∈ Subgroup.normalizer (K : Set G) ↔ bf x ⟨z, hzD⟩ = 0 :=
    fun x => (hbf.spec K c.twin.mem ⟨z, hzD⟩ c.twin.isInv x).symm
  have hclos := Polar.Sections.closure_nbr_eq hbf.sympForm hPS hSec hcard hpP
  have hEs_le : Subgroup.closure (insert (⟨z, hzD⟩ : zGroup Ω)
      (Polar.nbr bf (zPoints Ω) ⟨z, hzD⟩)) ≤ (eGroup Ω K).subgroupOf (zGroup Ω) := by
    refine Subgroup.closure_le _ |>.mpr ?_
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨K, Set.mem_insert _ _,
        c.twin.isInv⟩)
    · have hyP : y.1 ∈ zSet Ω := hy.1
      obtain ⟨g', hg'⟩ := (EndHyp.mem_zSet_iff h c.twin).mp hyP
      have hyN : y.1 ∈ Subgroup.normalizer (K : Set G) := (hN y).mpr (by
        rw [hbf.symm]; exact hy.2.2)
      exact Subgroup.mem_subgroupOf.mpr
        ((h.mem_eGroup_iff_mem_normalizer h9 c.twin.mem c.twin.isInv ⟨g', hg'⟩).mpr hyN)
  have hEq : zGroup Ω ⊓ Subgroup.normalizer (K : Set G) = eGroup Ω K := by
    ext x
    constructor
    · rintro ⟨hxD, hxN⟩
      have hx0 : bf ⟨z, hzD⟩ ⟨x, hxD⟩ = 0 := by
        rw [hbf.symm]
        exact (hN ⟨x, hxD⟩).mp hxN
      have hx' : (⟨x, hxD⟩ : zGroup Ω) ∈
          Subgroup.closure (insert (⟨z, hzD⟩ : zGroup Ω) (Polar.nbr bf (zPoints Ω) ⟨z, hzD⟩)) := by
        have hmem : (⟨x, hxD⟩ : zGroup Ω) ∈ ({x' | bf ⟨z, hzD⟩ x' = 0} : Set (zGroup Ω)) := hx0
        rw [← hclos] at hmem
        exact hmem
      exact Subgroup.mem_subgroupOf.mp (hEs_le hx')
    · intro hx
      exact ⟨hED hx, h.eGroup_le_normalizer c.twin.mem hx⟩
  refine ⟨hEq, ?_⟩
  have hmemEs : ∀ x : zGroup Ω, x ∈ (eGroup Ω K).subgroupOf (zGroup Ω) ↔
      bf x ⟨z, hzD⟩ = 0 := by
    intro x
    rw [Subgroup.mem_subgroupOf, ← hEq]
    exact ⟨fun hx => (hN x).mp (Subgroup.mem_inf.mp hx).2,
      fun hx => Subgroup.mem_inf.mpr ⟨x.2, (hN x).mpr hx⟩⟩
  obtain ⟨a, ha⟩ : ∃ a : zGroup Ω, bf a ⟨z, hzD⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply c.twin.isInv.ne_one
    have h1 : (⟨z, hzD⟩ : zGroup Ω) = 1 :=
      hbf.nondeg _ (fun b => by rw [hbf.symm]; exact hcon b)
    exact congrArg Subtype.val h1
  have hZ2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
  have ha1 : bf a ⟨z, hzD⟩ = 1 := hZ2 _ ha
  have hidx : ((eGroup Ω K).subgroupOf (zGroup Ω)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨a, fun b => ?_⟩
    rw [hmemEs (b * a), hmemEs b, hbf.mul_left b a ⟨z, hzD⟩, ha1]
    generalize bf b ⟨z, hzD⟩ = t
    revert t
    decide
  have hcardE : Nat.card ↥((eGroup Ω K).subgroupOf (zGroup Ω)) = Nat.card ↥(eGroup Ω K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv
  have hm := Subgroup.card_mul_index ((eGroup Ω K).subgroupOf (zGroup Ω))
  rw [hidx, hcardE] at hm
  omega

end Sit16

end CFSG.ClassicalInvolution.Q3.Sec13
