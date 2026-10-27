module

public import CFSG.ClassicalInvolution.Q3.TL3T33
public import CFSG.ClassicalInvolution.Q3.TL4D1ME8D
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLF
public import CFSG.ClassicalInvolution.Q3.TL4D1MAME

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TL4 Matrix

section Translations

@[expose] noncomputable def translSub : Subgroup (Equiv.Perm (Fin 8)) :=
  linHom.ker.map agl32.subtype

theorem exists_eq_aperm_of_mem_translSub {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ translSub) :
    ∃ b, σ = aperm 1 b := by
  obtain ⟨τ, hτ, rfl⟩ := hσ
  have h1 : linPart τ = 1 := hτ
  refine ⟨transPart τ, ?_⟩
  calc agl32.subtype τ = aperm (linPart τ) (transPart τ) := (aperm_linPart τ).symm
    _ = aperm 1 (transPart τ) := by rw [h1]

theorem aperm_one_mem_translSub (b : Fin 3 → ZMod 2) : aperm 1 b ∈ translSub :=
  ⟨⟨aperm 1 b, aperm_mem_agl32 1 b⟩, linPart_eq rfl, rfl⟩

theorem translSub_normal {g σ : Equiv.Perm (Fin 8)} (hg : g ∈ agl32) (hσ : σ ∈ translSub) :
    g * σ * g⁻¹ ∈ translSub := by
  obtain ⟨τ, hτ, rfl⟩ := hσ
  refine ⟨⟨g, hg⟩ * τ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  show linHom (⟨g, hg⟩ * τ * ⟨g, hg⟩⁻¹) = 1
  rw [map_mul, map_mul, map_inv, show linHom τ = 1 from hτ, mul_one, mul_inv_cancel]

theorem translSub_isPGroup : IsPGroup 2 ↥translSub := fun σ => ⟨1, by
  obtain ⟨b, hb⟩ := exists_eq_aperm_of_mem_translSub σ.2
  rw [pow_one, pow_two]
  refine Subtype.ext ?_
  show (σ : Equiv.Perm (Fin 8)) * σ = 1
  rw [hb, aperm_one_mul_self]⟩

theorem le_translSub_of_normal {Q : Subgroup (Equiv.Perm (Fin 8))} (hQ : Q ≤ agl32)
    (hQn : ∀ g ∈ agl32, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) (h2 : IsPGroup 2 ↥Q) : Q ≤ translSub := by
  set L := (Q.subgroupOf agl32).map linHom with hL
  have hLn : L.Normal := by
    refine ⟨fun x hx A => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hx
    let g : ↥agl32 := ⟨aperm A 0, aperm_mem_agl32 A 0⟩
    have hg : linHom g = A := linPart_eq rfl
    refine ⟨g * q * g⁻¹,
      Subgroup.mem_subgroupOf.mpr (hQn _ g.2 _ (Subgroup.mem_subgroupOf.mp hq)), ?_⟩
    rw [map_mul, map_mul, map_inv, hg]
  have hs := isSimpleGroup_sl3Two
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hbot | htop
  · intro q hq
    refine ⟨⟨q, hQ hq⟩, ?_, rfl⟩
    have : linHom ⟨q, hQ hq⟩ ∈ L := ⟨⟨q, hQ hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  · exfalso
    have hL2 : IsPGroup 2 ↥L := h2.comap_subtype.map _
    have hA : sl3A ∈ L := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := hL2 ⟨sl3A, hA⟩
    have hk' : sl3A ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : orderOf sl3A ∣ 3 := orderOf_dvd_of_pow_eq_one sl3A_pow_three
    have h2k : orderOf sl3A ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exact sl3A_ne_one (orderOf_eq_one_iff.mp h1)
    · rw [h1] at h2k
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2k) (by norm_num)

theorem aperm_one_symm_apply (b : Fin 3 → ZMod 2) (i : Fin 8) :
    (aperm 1 b).symm i = binIdx (bin i + b) := by
  have h : (aperm 1 b)⁻¹ = aperm 1 b := inv_eq_of_mul_eq_one_left (aperm_one_mul_self b)
  rw [← Equiv.Perm.inv_def, h, aperm_apply]
  unfold aapply
  rw [show (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)).1 = 1 from rfl, one_mulVec]

end Translations

section E29

@[expose] noncomputable def nBar : Subgroup (AEQ 8) := e29Sub ⊓ translSub.comap (permQ 8)

theorem nBar_normal : ∀ x ∈ e29Sub, ∀ t ∈ nBar, x * t * x⁻¹ ∈ nBar := by
  intro x hx t ht
  refine ⟨e29Sub.mul_mem (e29Sub.mul_mem hx ht.1) (e29Sub.inv_mem hx), ?_⟩
  show permQ 8 (x * t * x⁻¹) ∈ translSub
  rw [map_mul, map_mul, map_inv]
  exact translSub_normal (permQ_mem_of_mem_aeBarOver (A := agl32) hx) ht.2

theorem ker_permQ_isPGroup (n : ℕ) : IsPGroup 2 ↥(permQ n).ker := fun t => ⟨1, by
  rw [pow_one, pow_two]
  exact Subtype.ext (mul_self_of_mem_ker_permQ t.2)⟩

theorem nBar_isPGroup : IsPGroup 2 ↥nBar :=
  (translSub_isPGroup.comap_of_ker_isPGroup (permQ 8) (ker_permQ_isPGroup 8)).to_le inf_le_right

theorem le_nBar_of_normal {T : Subgroup (AEQ 8)} (hTM : T ≤ e29Sub)
    (hTn : ∀ x ∈ e29Sub, ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hT2 : IsPGroup 2 ↥T) : T ≤ nBar := by
  intro t ht
  refine ⟨hTM ht, ?_⟩
  show permQ 8 t ∈ translSub
  refine le_translSub_of_normal (Q := T.map (permQ 8)) ?_ ?_ (hT2.map _) ⟨t, ht, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact permQ_mem_of_mem_aeBarOver (A := agl32) (hTM hs)
  · rintro σ hσ _ ⟨s, hs, rfl⟩
    refine ⟨mkQ 8 (ofPerm σ) * s * (mkQ 8 (ofPerm σ))⁻¹,
      hTn _ (mkQ_ofPerm_mem_aeBarOver hσ ?_) s hs, ?_⟩
    · exact Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign σ hσ)
    · rw [map_mul, map_mul, map_inv, permQ_mkQ]
      rfl

@[expose] def ind (α : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun x => if x ∈ α then 1 else 0

theorem zBar_eq_vbar (α : Finset (Fin 8)) (h : α.card = 4) : zBar α h = vbar 8 (ind α) := by
  rw [zBar, vbar]
  congr 1
  refine Wr.ext (funext fun x => ?_) (zOf_perm _)
  have hr : x ∈ Set.range (emb α h) ↔ x ∈ α := by rw [range_emb]; rfl
  rw [zOf_vec_apply]
  show _ = if x ∈ α then 1 else 0
  by_cases hx : x ∈ α
  · have : x ∈ Set.range (emb α h) := hr.mpr hx
    simp [this, hx]
  · have : x ∉ Set.range (emb α h) := fun h' => hx (hr.mp h')
    simp [this, hx]

theorem transl_ind_plane : ∀ b : Fin 3 → ZMod 2, ∀ α ∈ affinePlanes,
    (fun i => ind α (binIdx (bin i + b))) = ind α ∨
      (fun i => ind α (binIdx (bin i + b))) = ind α + 1 := by
  decide +kernel

theorem affinePlanes_card : ∀ α ∈ affinePlanes, α.card = 4 := by decide +kernel

theorem affinePlanes_compl : ∀ α ∈ affinePlanes, αᶜ ∈ affinePlanes := by decide +kernel

theorem transl_fixed : ∀ u : Fin 8 → ZMod 2,
    (∀ b : Fin 3 → ZMod 2, (fun i => u (binIdx (bin i + b))) = u ∨
      (fun i => u (binIdx (bin i + b))) = u + 1) →
    (u = 0 ∨ u = 0 + 1) ∨ ∃ α ∈ affinePlanes, u = ind α ∨ u = ind α + 1 := by
  decide +kernel

theorem det_singer : det3 !![0, 0, 1; 1, 0, 1; 0, 1, 0] = 1 := by decide

theorem agl_fixed : ∀ u : Fin 8 → ZMod 2,
    (∀ b : Fin 3 → ZMod 2, (fun i => u (binIdx (bin i + b))) = u ∨
      (fun i => u (binIdx (bin i + b))) = u + 1) →
    ((fun i => u (binIdx (!![0, 0, 1; 1, 0, 1; 0, 1, 0] *ᵥ bin i))) = u ∨
      (fun i => u (binIdx (!![0, 0, 1; 1, 0, 1; 0, 1, 0] *ᵥ bin i))) = u + 1) →
    u = 0 ∨ u = 0 + 1 := by
  decide +kernel

theorem perm_eq_one_of_modPi {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : ∀ p q : Fin n, p ≠ q → ModPi (actV σ (pairVec p q)) (pairVec p q)) : σ = 1 := by
  refine Equiv.ext fun p => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  obtain ⟨q, hqp, hqσ, -, -⟩ := exists_ne_four hn p (σ p) p p
  have := eq_of_modPi_pairVec hn (Ne.symm hqp) hne (by rw [← actV_pairVec]; exact h p q (Ne.symm hqp))
  exact hqσ this.symm

theorem perm_eq_one_of_comm_nBar {a : Wr 8}
    (h : ∀ t ∈ nBar, mkQ 8 a * t = t * mkQ 8 a) : a.perm = 1 := by
  refine perm_eq_one_of_modPi (by norm_num) fun p q _ => ?_
  have hv : vbar 8 (pairVec p q) ∈ nBar := ⟨vbar_mem_aeBarOver (sum_pairVec p q), by
    show permQ 8 (vbar 8 (pairVec p q)) ∈ translSub
    exact translSub.one_mem⟩
  have h1 : mkQ 8 a * vbar 8 (pairVec p q) * (mkQ 8 a)⁻¹ = vbar 8 (pairVec p q) := by
    rw [h _ hv, mul_inv_cancel_right]
  rw [conj_vbar (permBar_mkQ a)] at h1
  exact vbar_eq_iff.mp h1

theorem modPi_transl_of_comm {u : Fin 8 → ZMod 2}
    (h : ∀ t ∈ nBar, vbar 8 u * t = t * vbar 8 u) (b : Fin 3 → ZMod 2) :
    (fun i => u (binIdx (bin i + b))) = u ∨ (fun i => u (binIdx (bin i + b))) = u + 1 := by
  have ht : mkQ 8 (ofPerm (aperm 1 b)) ∈ nBar :=
    ⟨mkQ_ofPerm_mem_aeBarOver (aperm_mem_agl32 1 b)
      (Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign _ (aperm_mem_agl32 1 b))),
      aperm_one_mem_translSub b⟩
  have h1 : mkQ 8 (ofPerm (aperm 1 b)) * vbar 8 u * (mkQ 8 (ofPerm (aperm 1 b)))⁻¹ =
      vbar 8 u := by
    rw [← h _ ht, mul_inv_cancel_right]
  rw [conj_vbar (permBar_mkQ (ofPerm (aperm 1 b))), vbar_eq_iff] at h1
  have e : actV (ofPerm (aperm 1 b)).perm u = fun i => u (binIdx (bin i + b)) := by
    funext i
    show u ((aperm 1 b).symm i) = _
    rw [aperm_one_symm_apply]
  rw [e] at h1
  exact h1

theorem e29_center : ModelCenter e29Sub := by
  intro m hm hc
  obtain ⟨a, rfl⟩ : ∃ a, mkQ 8 a = m := QuotientGroup.mk_surjective m
  have hσ : a.perm = 1 := perm_eq_one_of_comm_nBar fun t ht => hc t ht.1
  obtain ⟨u, hu⟩ := exists_vbar_of_permBar_eq_one
    (show permBar 8 (mkQ 8 a) = 1 by rw [permBar_mkQ, hσ])
  rw [hu] at hc ⊢
  have hfix : ∀ σ ∈ agl32, ModPi (actV σ u) u := fun σ hσ' => by
    have hσM : mkQ 8 (ofPerm σ) ∈ e29Sub :=
      mkQ_ofPerm_mem_aeBarOver hσ' (Equiv.Perm.mem_alternatingGroup.mpr (agl32_sign σ hσ'))
    have h1 : mkQ 8 (ofPerm σ) * vbar 8 u * (mkQ 8 (ofPerm σ))⁻¹ = vbar 8 u := by
      rw [← hc _ hσM, mul_inv_cancel_right]
    rw [conj_vbar (permBar_mkQ (ofPerm σ))] at h1
    exact vbar_eq_iff.mp h1
  set A₀ := slOf !![0, 0, 1; 1, 0, 1; 0, 1, 0] det_singer with hA₀
  have h0 := hfix _ (agl32.inv_mem (aperm_mem_agl32 A₀ 0))
  have e : actV (aperm A₀ 0)⁻¹ u = fun i => u (binIdx (!![0, 0, 1; 1, 0, 1; 0, 1, 0] *ᵥ bin i)) := by
    funext i
    show u ((aperm A₀ 0)⁻¹.symm i) = _
    rw [Equiv.Perm.inv_def, Equiv.symm_symm, aperm_apply]
    unfold aapply
    rw [add_zero, hA₀, slOf_val]
  rw [e] at h0
  have hu0 := agl_fixed u (modPi_transl_of_comm fun t ht => hc t ht.1) h0
  rw [← vbar_zero]
  exact vbar_eq_iff.mpr hu0

theorem e29_invO2 : ModelInvO2 e29Sets e29Sub := by
  intro α hα h T hTM hTn hT2 t ht
  have htN := le_nBar_of_normal hTM hTn hT2 ht
  obtain ⟨a, rfl⟩ : ∃ a, mkQ 8 a = t := QuotientGroup.mk_surjective t
  obtain ⟨b, hb⟩ := exists_eq_aperm_of_mem_translSub htN.2
  have hconj : mkQ 8 a * zBar α h * (mkQ 8 a)⁻¹ = zBar α h := by
    rw [zBar_eq_vbar, conj_vbar (permBar_mkQ a), vbar_eq_iff]
    have e : actV a.perm (ind α) = fun i => ind α (binIdx (bin i + b)) := by
      funext i
      show ind α (a.perm.symm i) = _
      rw [show a.perm = aperm 1 b from hb, aperm_one_symm_apply]
    rw [e]
    exact transl_ind_plane b α hα
  calc zBar α h * mkQ 8 a = mkQ 8 a * zBar α h * (mkQ 8 a)⁻¹ * mkQ 8 a := by rw [hconj]
    _ = mkQ 8 a * zBar α h := by group

theorem e29_twCoreZ : ModelTwCoreZ e29Sets e29Sub := by
  intro B w hBM hBw hB8 hBnc hZw hthin hi
  classical
  have hwN : ∀ t ∈ nBar, w * t = t * w := hZw nBar inf_le_left nBar_normal nBar_isPGroup
  obtain ⟨a, rfl⟩ : ∃ a, mkQ 8 a = w := QuotientGroup.mk_surjective w
  have hσ : a.perm = 1 := perm_eq_one_of_comm_nBar hwN
  obtain ⟨u, hu⟩ := exists_vbar_of_permBar_eq_one
    (show permBar 8 (mkQ 8 a) = 1 by rw [permBar_mkQ, hσ])
  have hwE : permQ 8 (mkQ 8 a) = 1 := hσ
  rw [hu] at hwN
  obtain ⟨α, hα, hαu⟩ : ∃ α ∈ affinePlanes, ModPi u (ind α) := by
    rcases transl_fixed u (modPi_transl_of_comm hwN) with h0 | h0
    · exfalso
      apply hBw.ne_one
      rw [hu, ← vbar_zero]
      exact vbar_eq_iff.mpr h0
    · exact h0
  have hα4 := affinePlanes_card α hα
  have hwz : mkQ 8 a = zBar α hα4 := by
    rw [hu, zBar_eq_vbar]
    exact vbar_eq_iff.mpr hαu
  set M := e29Sub with hM
  set E : Subgroup (AEQ 8) := M ⊓ (permQ 8).ker with hE
  have hEn : ∀ x ∈ M, ∀ t ∈ E, x * t * x⁻¹ ∈ E := by
    intro x hx t ht
    refine ⟨M.mul_mem (M.mul_mem hx ht.1) (M.inv_mem hx), ?_⟩
    show permQ 8 (x * t * x⁻¹) = 1
    rw [map_mul, map_mul, map_inv, show permQ 8 t = 1 from ht.2, mul_one, mul_inv_cancel]
  have hthinE : ∀ x ∈ B, permQ 8 x = 1 → x = 1 ∨ x = mkQ 8 a :=
    fun x hx hx1 => hthin E inf_le_left hEn ((ker_permQ_isPGroup 8).to_le inf_le_right) x hx
      ⟨hBM hx, hx1⟩
  obtain ⟨hwc, -⟩ := q8_facts hBw hB8 hBnc
  have hpres : ∀ c : Wr 8, mkQ 8 c ∈ B → mkQ 8 c ≠ 1 → mkQ 8 c ≠ mkQ 8 a →
      ∀ x, c.perm x ∈ α ↔ x ∈ α := by
    intro c hc hc1 hcw x
    have hcc : mkQ 8 (c * c) = vbar 8 (ind α) := by
      rw [map_mul, sq_eq_of_isUniqueInvolution hBw hB8 hBnc hc hc1 hcw, hwz, zBar_eq_vbar]
    have hp : c.perm * c.perm = 1 := by
      have := congrArg (permQ 8) hcc
      rwa [permQ_mkQ, show permQ 8 (vbar 8 (ind α)) = 1 from rfl] at this
    have hcv : c * c = ofVec (c * c).vec := Wr.ext rfl hp
    rw [hcv] at hcc
    have hm : ModPi (c * c).vec (ind α) := vbar_eq_iff.mp hcc
    have hsymm : ∀ y, c.perm.symm y = c.perm y := fun y => by
      rw [← Equiv.Perm.inv_def, inv_eq_of_mul_eq_one_left hp]
    have hinv : ∀ y, (c * c).vec (c.perm y) = (c * c).vec y := fun y => by
      rw [mul_vec, mul_vec, hsymm, hsymm, ← Equiv.Perm.mul_apply, hp, Equiv.Perm.one_apply,
        add_comm]
    have key : ind α (c.perm x) = ind α x := by
      rcases hm with h | h
      · rw [← h]
        exact hinv x
      · have h1 := hinv x
        rw [h] at h1
        simpa using h1
    unfold ind at key
    constructor
    · intro hcx
      by_contra hx
      simp [hcx, hx] at key
    · intro hx
      by_contra hcx
      simp [hcx, hx] at key
  refine false_of_twCore (n := 8) (by norm_num) (A := agl32) hBM hBw hB8 hBnc hwE hthinE
    (fun a' b' hx hy hxy => ?_) hi
  have hnc_of : ∀ g ∈ B, g = 1 ∨ g = mkQ 8 a → ∀ g' ∈ B, g * g' = g' * g := by
    rintro g - (rfl | rfl) g' hg'
    · rw [one_mul, mul_one]
    · exact (hwc g' hg').symm
  have hpa := hpres a' hx (fun h => hxy (hnc_of _ hx (Or.inl h) _ hy))
    (fun h => hxy (hnc_of _ hx (Or.inr h) _ hy))
  have hpb := hpres b' hy (fun h => hxy (hnc_of _ hy (Or.inl h) _ hx).symm)
    (fun h => hxy (hnc_of _ hy (Or.inr h) _ hx).symm)
  by_cases hmov : ∃ x ∈ α, a'.perm x ≠ x ∨ b'.perm x ≠ x
  · exact ⟨α, hα, hα4, fun x hx' => (hpa x).mpr hx', fun x hx' => (hpb x).mpr hx', hmov⟩
  · push Not at hmov
    have ha1 : a'.perm ≠ 1 := fun h =>
      hxy (hnc_of _ hx (hthinE _ hx (by rw [permQ_mkQ, h])) _ hy)
    obtain ⟨x, hx'⟩ : ∃ x, a'.perm x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact ha1 (Equiv.ext hcon)
    have hxα : x ∉ α := fun h => hx' (hmov x h).1
    refine ⟨αᶜ, affinePlanes_compl α hα, by rw [Finset.card_compl, hα4]; rfl,
      fun y hy => ?_, fun y hy => ?_, x, Finset.mem_compl.mpr hxα, Or.inl hx'⟩
    · rw [Finset.mem_compl] at hy ⊢
      exact fun h => hy ((hpa y).mp h)
    · rw [Finset.mem_compl] at hy ⊢
      exact fun h => hy ((hpb y).mp h)

end E29

theorem d1TwFacts_holds : D1TwFacts where
  e8Normal := TL4.e8NormalFact
  e8Perfect := TL4.e8PerfectFact
  aeNormal := TL4.aeNormal
  aePerfect := TL4.aePerfect
  aeCore := modelTwCore_aeModel
  e64Normal := TL4.e64_normal
  e64Perfect := TL4.e64_perfect
  e64Three := TL4.e64_three
  e64Core := modelTwCore_e64
  e29Normal := TL4.e29_normal
  e29Perfect := TL4.e29_perfect
  e29Three := TL4.e29_three
  e29Center := e29_center
  e29Inv := e29_invO2
  e29CoreZ := e29_twCoreZ

theorem d1GenLeaf_holds (r : ℕ) : D1GenLeaf r := d1GenLeaf_of_facts d1TwFacts_holds r

variable {r : ℕ} {IH : ℕ → Prop}

theorem dLeafC_of₄ (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH) (hE29 : CLeafE29 r IH)
    (hAE : CLeafAE r IH) : DLeafC r IH :=
  dLeafC_of₃ d1TwFacts_holds hE8 hE64 hE29 hAE

theorem thmDAbs_of_leaves₇ (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH) (hE29 : CLeafE29 r IH)
    (hAE : CLeafAE r IH) (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH) (hend : DLeafEnd r IH)
    (hih : ∀ n, IH n) : ThmDAbs r :=
  thmDAbs_of_leaves₆ d1TwFacts_holds hE8 hE64 hE29 hAE hE4 hstar hend hih

section Cit3


theorem thmD2Step_of_leaves₆ (hE8 : CLeafE8 r (PackIH r)) (hE64 : CLeafE64 r (PackIH r))
    (hE29 : CLeafE29 r (PackIH r)) (hAE : CLeafAE r (PackIH r)) (hE4 : DLeafE4 r (PackIH r))
    (hstar : DLeafStar r (PackIH r)) (hend : DLeafEnd r (PackIH r)) (n : ℕ) :
    CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) :=
  thmD2Step_of_leaves₅ d1TwFacts_holds hE8 hE64 hE29 hAE hE4 hstar hend n

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
