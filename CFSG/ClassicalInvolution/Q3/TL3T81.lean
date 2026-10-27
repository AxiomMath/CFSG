module

public import CFSG.ClassicalInvolution.Q3.TL3T64
public import CFSG.ClassicalInvolution.Q3.TL3T73
public import CFSG.ClassicalInvolution.Q3.TL3T63

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

theorem allOnes_not_mem_aeSub {k : ℕ} (hk : Odd k) : allOnes k ∉ aeSub k := by
  intro h
  have h1 : wsum (allOnes k) = 0 := h.1
  have h2 : wsum (allOnes k) = (k : ZMod 2) := by
    simp [wsum, allOnes]
  have h3 : (k : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hk
  rw [h2, h3] at h1
  exact absurd h1 (by decide)

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section Sub

variable {G : Type} [Group G] [Finite G] {P Q : Set (Subgroup G)} {n k : ℕ}

theorem SubHyp.subQ_mem_range_θ {I : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    (hk : 5 ≤ k) (hodd : Odd k) {w : Wr k} (hw : w ∈ aeSub k) : subQ c w ∈ h.θ.range := by
  have hmem : mkQ k w ∈ (I.restrict hk h).φ.range := by
    rw [(I.restrict hk h).range_eq]
    exact ⟨w, hw, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  rw [AEIdent.restrict_apply] at hx
  have hpre : h.pre x = w := by
    rcases mkQ_eq_iff.mp hx with h1 | h1
    · exact inv_mul_eq_one.mp h1
    · exfalso
      refine allOnes_not_mem_aeSub hodd ?_
      rw [← h1]
      exact (aeSub k).mul_mem ((aeSub k).inv_mem (h.pre_mem x)) hw
  exact ⟨x, by rw [← h.subQ_pre x, hpre]⟩

end Sub

section Aux

private theorem exists_lift_pow_three_of_hom {H B : Type*} [Group H] [Group B] [Finite H]
    (f : H →* B) {x : B} (hx : x ∈ f.range) (hx3 : x ^ 3 = 1) :
    ∃ y : H, f y = x ∧ ∃ a : ℕ, y ^ 3 ^ a = 1 := by
  obtain ⟨y₀, rfl⟩ := hx
  obtain ⟨a, r, hr, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' 3 (by norm_num)
  refine ⟨y₀ ^ (r * r), ?_, a, ?_⟩
  · have hr2 : r * r % 3 = 1 := by
      have : r % 3 = 1 ∨ r % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, pow_eq_pow_mod _ hx3, hr2, pow_one]
  · rw [← pow_mul, show r * r * 3 ^ a = (3 ^ a * r) * r by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

private theorem pow_three_pow_eq_one_of_le {H : Type*} [Monoid H] {x : H} {a b : ℕ} (hab : a ≤ b)
    (h : x ^ 3 ^ a = 1) : x ^ 3 ^ b = 1 := by
  obtain ⟨t, ht⟩ := pow_dvd_pow 3 hab
  rw [ht, pow_mul, h, one_pow]

private theorem exists_threeCycle : ∀ a c : Fin 5, a ≠ c → ∃ σ : Equiv.Perm (Fin 5),
    σ a = a ∧ σ c = c ∧ σ * σ * σ = 1 ∧ ∀ p, p ≠ a → p ≠ c → σ p ≠ p := by
  decide +kernel

private theorem memBar_congr' {N : ℕ} {α β : Finset (Fin N)} (e : α = β) (h : α.card = 4)
    (h' : β.card = 4) (b : Bool) : memBar α h b = memBar β h' b := by
  subst e
  rfl

private theorem apply_eq_of_map_eq {N : ℕ} (Φ : Fin 5 ↪ Fin N) (ρ : Equiv.Perm (Fin N))
    (τ : Equiv.Perm (Fin 5))
    (h : ∀ α : Finset (Fin 5), α.card = 4 →
      (α.map Φ).map ρ.toEmbedding = (α.map τ.toEmbedding).map Φ) (i : Fin 5) :
    ρ (Φ i) = Φ (τ i) := by
  classical
  have key : ∀ j : Fin 5, j ≠ i → ∃ s : Fin 5, s ≠ j ∧ Φ (τ s) = ρ (Φ i) := by
    intro j hj
    have hcard : (Finset.univ.erase j).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
      simp
    have hmem : ρ (Φ i) ∈ ((Finset.univ.erase j).map Φ).map ρ.toEmbedding :=
      Finset.mem_map_of_mem _ (Finset.mem_map_of_mem _
        (Finset.mem_erase.mpr ⟨hj.symm, Finset.mem_univ i⟩))
    rw [h _ hcard] at hmem
    obtain ⟨t, ht, hts⟩ := Finset.mem_map.mp hmem
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    exact ⟨s, (Finset.mem_erase.mp hs).1, hts⟩
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  obtain ⟨s₀, -, hs₀⟩ := key j₀ hj₀
  by_contra hne
  have hs₀i : s₀ ≠ i := by
    rintro rfl
    exact hne hs₀.symm
  obtain ⟨s, hsne, hs⟩ := key s₀ hs₀i
  exact hsne (τ.injective (Φ.injective (hs.trans hs₀.symm)))

private theorem embW_mem_aeSub_iff {k N : ℕ} (c : Fin k ↪ Fin N) (w : Wr k) :
    embW c w ∈ aeSub N ↔ w ∈ aeSub k := by
  have h1 : wsum (embW c w) = wsum w := by
    unfold wsum
    rw [embW_vec]
    exact sum_embWVec c w.vec
  have h2 : Equiv.Perm.sign (embW c w).perm = Equiv.Perm.sign w.perm := by
    rw [embW_perm]
    classical
    unfold embWPerm
    exact Equiv.Perm.sign_extendDomain _ _
  exact ⟨fun h => ⟨h1 ▸ h.1, h2 ▸ h.2⟩, fun h => ⟨h1.trans h.1, h2.trans h.2⟩⟩

private theorem exists_embW_eq {k N : ℕ} (c : Fin k ↪ Fin N) {y : Wr N}
    (hy : SupportedOn y (Set.range c)) : ∃ y' : Wr k, embW c y' = y := by
  classical
  obtain ⟨τ, hτ⟩ := exists_extendPerm_eq c (σ := y.perm) fun x hx => (hy x hx).2
  refine ⟨⟨fun i => y.vec (c i), τ⟩, Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)⟩
  · by_cases hx : x ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hx
      exact embWVec_apply c _ i
    · rw [embW_vec, embWVec_of_not_mem c _ hx, (hy x hx).1]
  · by_cases hx : x ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hx
      rw [embW_perm, embWPerm_apply, ← hτ, extendPerm_apply]
    · rw [embW_perm, embWPerm_of_not_mem c _ hx, (hy x hx).2]

private theorem perm_fix_of_comm_memBar {N : ℕ} {w : Wr N} (hw : ∃ k : ℕ, w.perm ^ 3 ^ k = 1)
    {β : Finset (Fin N)} {hβ : β.card = 4} {b : Bool}
    (hc : ∀ x ∈ memBar β hβ b, mkQ N w * x = x * mkQ N w) : ∀ x ∈ β, w.perm x = x := by
  have key : ∀ d ∈ [d₁, d₂, d₃],
      w.perm * embedPerm (emb β hβ) d = embedPerm (emb β hβ) d * w.perm := by
    intro d hd
    obtain ⟨k, hk, hkd⟩ := exists_kList_perm b d hd
    have hmem : mkQ N (embed (emb β hβ) k) ∈ memBar β hβ b := by
      refine ⟨embed (emb β hβ) k, ?_, rfl⟩
      cases b
      · exact ⟨k, hk, rfl⟩
      · exact ⟨k, hk, rfl⟩
    have h := congrArg (permQ N) (hc _ hmem)
    rwa [map_mul, map_mul, permQ_mkQ, permQ_mkQ, embed_perm, hkd] at h
  have hfe := fix_of_comm_embedPerm (emb β hβ) hw (key d₁ (by simp)) (key d₂ (by simp))
    (key d₃ (by simp))
  intro x hx
  have hxr : x ∈ Set.range (emb β hβ) := by
    rw [range_emb]
    exact_mod_cast hx
  obtain ⟨i, rfl⟩ := hxr
  exact hfe i

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G}

private theorem exists_move_element {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5}
    (D : PairChart Ω K J I) {c₁ : Fin 5 ↪ Fin (5 + 2)}
    (hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c)
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) c₁) :
    ∃ (m : G) (y : Wr 5) (e : ℕ) (hm : m ∈ pSpan (centMembers Ω D.u)),
      m ∈ pSpan (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) ∧
      m ∈ pSpan (orbOf (TC.nbrAdj Ω) K J) ∧ m ^ 3 ^ e = 1 ∧
      D.IY.φ ⟨m, hm⟩ = mkQ (5 + 2) (embW c₁ y) ∧
      ∀ i, c₁ i ∈ Finset.univ.map D.ι → y.perm i ≠ i := by
  classical
  have hodd : Odd 5 := ⟨2, rfl⟩
  obtain ⟨σ, hσa, hσc, hσ3, hσmove⟩ := exists_threeCycle D.a D.c D.hac
  have hσ3' : σ ^ 3 = 1 := by rw [pow_three']; exact hσ3
  have hσsign : Equiv.Perm.sign σ = 1 := by
    have h3 : Equiv.Perm.sign σ ^ 3 = 1 := by rw [← map_pow, hσ3', map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · rw [h] at h3
      exact absurd h3 (by decide)
  have hσA : ofPerm σ ∈ aeSub 5 := ⟨by simp [wsum, ofPerm], hσsign⟩
  have hx : subQ D.ι (ofPerm σ) ∈ D.hsub.θ.range :=
    D.hsub.subQ_mem_range_θ le_rfl hodd hσA
  have hx3 : subQ D.ι (ofPerm σ) ^ 3 = 1 := by
    rw [← map_pow, ofPerm_pow, hσ3', ofPerm_one, map_one]
  obtain ⟨m₁, hm₁, e₁, hme₁⟩ := exists_lift_pow_three_of_hom D.hsub.θ hx hx3
  have hmY : (m₁ : G) ∈ pSpan (centMembers Ω D.u) := D.hsub.span_le m₁.2
  have hφm : D.IY.φ ⟨(m₁ : G), hmY⟩ = subQ D.ι (ofPerm σ) := hm₁
  have hme : (m₁ : G) ^ 3 ^ e₁ = 1 := by
    have := congrArg Subtype.val hme₁
    simpa using this
  have hsupp : SupportedOn (embW D.ι (ofPerm σ)) (Set.range c₁) := by
    intro x hx
    have hx' : x = D.ι D.a ∨ x = D.ι D.c := by
      by_contra hcon
      push Not at hcon
      exact hx ((hc₁ x).mpr hcon)
    rcases hx' with rfl | rfl
    · exact ⟨by rw [embW_vec, embWVec_apply]; rfl, by
        rw [embW_perm, embWPerm_apply]; exact congrArg D.ι hσa⟩
    · exact ⟨by rw [embW_vec, embWVec_apply]; rfl, by
        rw [embW_perm, embWPerm_apply]; exact congrArg D.ι hσc⟩
  obtain ⟨y, hy⟩ := exists_embW_eq c₁ hsupp
  have hyA : y ∈ aeSub 5 :=
    (embW_mem_aeSub_iff c₁ y).mp (by rw [hy]; exact (embW_mem_aeSub_iff D.ι _).mpr hσA)
  have hsub : subQ c₁ y = subQ D.ι (ofPerm σ) := by rw [subQ_apply, subQ_apply, hy]
  have hxQ : subQ c₁ y ∈ h₁.θ.range := h₁.subQ_mem_range_θ le_rfl hodd hyA
  obtain ⟨o, ho, e₂, hoe₂⟩ := exists_lift_pow_three_of_hom h₁.θ hxQ (by rw [hsub]; exact hx3)
  have hk : IsPGroup 2 D.IY.φ.ker := D.hHY.ker_two
  have hmQ : (m₁ : G) ∈ pSpan (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) := by
    have hu : (Subgroup.inclusion h₁.span_le o : ↥(pSpan (centMembers Ω D.u))) ^
        3 ^ max e₁ e₂ = 1 := by
      rw [← map_pow, pow_three_pow_eq_one_of_le (le_max_right e₁ e₂) hoe₂, map_one]
    have hv : (⟨(m₁ : G), hmY⟩ : ↥(pSpan (centMembers Ω D.u))) ^ 3 ^ max e₁ e₂ = 1 := by
      refine Subtype.ext ?_
      simpa using pow_three_pow_eq_one_of_le (le_max_left e₁ e₂) hme
    have heq := D.IY.eq_of_map_eq_of_pow hk hu hv (by
      show h₁.θ o = D.IY.φ ⟨(m₁ : G), hmY⟩
      rw [ho, hsub, hφm])
    have h3 : (o : G) = (m₁ : G) := by
      have := congrArg Subtype.val heq
      simpa using this
    exact h3 ▸ o.2
  refine ⟨(m₁ : G), y, e₁, hmY, hmQ, m₁.2, hme, hφm.trans (by rw [subQ_apply, hy]), ?_⟩
  intro i hi hyi
  obtain ⟨x, -, hxi⟩ := Finset.mem_map.mp hi
  have hxa : x ≠ D.a := fun h' => ((hc₁ (c₁ i)).mp ⟨i, rfl⟩).1 (by rw [← hxi, h'])
  have hxc : x ≠ D.c := fun h' => ((hc₁ (c₁ i)).mp ⟨i, rfl⟩).2 (by rw [← hxi, h'])
  have hperm : embWPerm c₁ y.perm = embWPerm D.ι σ := congrArg Wr.perm hy
  have h1 := congrArg (fun p => p (c₁ i)) hperm
  simp only [embWPerm_apply] at h1
  rw [← hxi, embWPerm_apply] at h1
  rw [hyi] at h1
  have h2 : D.ι x = D.ι (σ x) := by rw [hxi]; exact h1
  exact hσmove x hxa hxc (D.ι.injective h2).symm

private theorem exists_chart_two_perm (hS : CSetting 3 IH Ω K J)
    {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5} (D : PairChart Ω K J I) {c₁ c₂ : Fin 5 ↪ Fin (5 + 2)}
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) c₁)
    (hZ₂ : D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ ⊆
      conjSub D.t '' centMembers Ω D.u)
    (hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin 5)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e')
    {m : G} (hm : m ∈ pSpan (centMembers Ω D.u))
    (hmQ : m ∈ pSpan (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ))
    (hmπ : m ∈ pSpan (orbOf (TC.nbrAdj Ω) K J)) {e : ℕ} (hme : m ^ 3 ^ e = 1) {y : Wr 5}
    (hφ : D.IY.φ ⟨m, hm⟩ = mkQ (5 + 2) (embW c₁ y)) :
    ∃ ρ : Equiv.Perm (Fin (5 + 2)), (∀ x ∈ D.γ.map D.ι, ρ x = x) ∧
      ∀ i, ρ (c₂ i) = c₂ (y.perm i) := by
  classical
  have hK : K ∈ Ω := hS.adj.1
  have hD := hS.cex.toThmDHyp
  have hmY₂ : m ∈ pSpan (conjSub D.t '' centMembers Ω D.u) :=
    (pSpan_le fun L hL => le_pSpan (hZ₂ hL)) hmQ
  have hx₂ : (D.IY.conjE D.t).φ ⟨m, hmY₂⟩ ∈ (D.IY.conjE D.t).φ.range := ⟨_, rfl⟩
  rw [(D.IY.conjE D.t).range_eq] at hx₂
  obtain ⟨w₂, hw₂, hw₂x⟩ := hx₂
  have hρ3 : ∃ k : ℕ, w₂.perm ^ 3 ^ k = 1 := by
    refine ⟨e, ?_⟩
    have h1 : (D.IY.conjE D.t).φ ⟨m, hmY₂⟩ ^ 3 ^ e = 1 := by
      rw [← map_pow]
      have : (⟨m, hmY₂⟩ : ↥(pSpan (conjSub D.t '' centMembers Ω D.u))) ^ 3 ^ e = 1 :=
        Subtype.ext (by simpa using hme)
      rw [this, map_one]
    rw [← hw₂x, ← map_pow] at h1
    have h2 : w₂ ^ 3 ^ e ∈ piSub (5 + 2) := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (w₂ ^ 3 ^ e).perm = 1 := by
      rcases mem_piSub.mp h2 with h | h <;> rw [h] <;> rfl
    rw [← h3]
    exact (map_pow (AE.permHom (5 + 2)) w₂ (3 ^ e)).symm
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJY : J ∈ centMembers Ω D.u := D.hπY hJπ
  obtain ⟨hγ', b₁, hlabJ₁⟩ := D.hlabι J hJπ D.γ D.hγ D.b D.hlabJ
  have hK₂ : K ∈ conjSub D.t '' centMembers Ω D.u := ⟨J, hJY, D.ht'⟩
  have hlabK₂ : (K.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map
      (D.IY.conjE D.t).φ = memBar (D.γ.map D.ι) hγ' b₁ := by
    have := (D.IY.map_conj D.t (L := J)).trans hlabJ₁
    rw [D.ht'] at this
    exact this
  have hKX : pSpan (orbOf (TC.nbrAdj Ω) K J) ≤ Subgroup.centralizer (K : Set G) :=
    hS.pSpan_orb_le.trans (pSpan_omegaNbr_le_centralizer hD.hyp hD.two hK)
  have hKm : ∀ l ∈ K, m * l = l * m := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hKX hmπ) l hl).symm
  have hcomm : ∀ x ∈ memBar (D.γ.map D.ι) hγ' b₁, mkQ (5 + 2) w₂ * x = x * mkQ (5 + 2) w₂ := by
    intro x hx
    rw [← hlabK₂] at hx
    obtain ⟨l, hl, rfl⟩ := (D.IY.conjE D.t).exists_of_mem_map hK₂ hx
    rw [hw₂x, ← map_mul, ← map_mul]
    exact congrArg (D.IY.conjE D.t).φ (Subtype.ext (hKm l hl))
  have hfix : ∀ x ∈ D.γ.map D.ι, w₂.perm x = x := perm_fix_of_comm_memBar hρ3 hcomm
  have hrel : ∀ α : Finset (Fin 5), α.card = 4 →
      (α.map c₂).map w₂.perm.toEmbedding = (α.map y.perm.toEmbedding).map c₂ := by
    intro α hα
    have hα₁ : (α.map c₁).card = 4 := by rw [Finset.card_map]; exact hα
    obtain ⟨M, hMQ, hMlab⟩ := h₁.surj α hα₁ true
    have hMY : M ∈ centMembers Ω D.u := h₁.sub hMQ
    have hM'Q := h₁.conj M hMQ m hmQ
    have hM'Y : conjSub m M ∈ centMembers Ω D.u := h₁.sub hM'Q
    have hα₂c : ((α.map y.perm.toEmbedding).map c₁).card = 4 := by
      rw [Finset.card_map, Finset.card_map]; exact hα
    obtain ⟨b₁', hb₁'⟩ := exists_conj_memBar_map (embW c₁ y) (α.map c₁) hα₁ true
    have h1 : ((conjSub m M).subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        conjSub (D.IY.φ ⟨m, hm⟩)
          ((M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ) :=
      TL4.AECov.map_conjSub_eq D.IY M ⟨m, hm⟩
    rw [hMlab, hφ, hb₁'] at h1
    have hmapeq : (α.map c₁).map (embW c₁ y).perm.toEmbedding =
        (α.map y.perm.toEmbedding).map c₁ := by
      rw [Finset.map_map, Finset.map_map]
      congr 1
      ext i
      simp [embW_perm, embWPerm_apply]
    have hlab1 : ((conjSub m M).subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ =
        memBar ((α.map y.perm.toEmbedding).map c₁) hα₂c b₁' :=
      h1.trans (memBar_congr' hmapeq _ _ _)
    obtain ⟨hα₂', e₂, hlab2⟩ := hcorr (conjSub m M) hM'Y _ hα₂c b₁' hlab1
    obtain ⟨hαM, e', hMlab₂⟩ := hcorr M hMY α hα₁ true hMlab
    obtain ⟨b₂, hb₂⟩ := exists_conj_memBar_map w₂ (α.map c₂) hαM e'
    have h2 : ((conjSub m M).subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map
        (D.IY.conjE D.t).φ = conjSub ((D.IY.conjE D.t).φ ⟨m, hmY₂⟩)
          ((M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ) :=
      TL4.AECov.map_conjSub_eq (D.IY.conjE D.t) M ⟨m, hmY₂⟩
    rw [hMlab₂, ← hw₂x, hb₂] at h2
    exact eq_of_memBar_eq' (by norm_num) (h2.symm.trans hlab2)
  exact ⟨w₂.perm, hfix, apply_eq_of_map_eq c₂ w₂.perm y.perm hrel⟩

theorem hmove_five (hS : CSetting 3 IH Ω K J) {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5}
    (D : PairChart Ω K J I) {c₁ c₂ : Fin 5 ↪ Fin (5 + 2)}
    (hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c)
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) c₁)
    (hZ₂ : D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ ⊆
      conjSub D.t '' centMembers Ω D.u)
    (hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin 5)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e') :
    ∀ i : Fin 5, c₁ i ∈ Finset.univ.map D.ι → c₂ i ∉ D.γ.map D.ι := by
  intro i hi hi₂
  obtain ⟨m, y, e, hm, hmQ, hmπ, hme, hφ, hmove⟩ := exists_move_element D hc₁ h₁
  obtain ⟨ρ, hρfix, hρ⟩ := exists_chart_two_perm hS D h₁ hZ₂ hcorr hm hmQ hmπ hme hφ
  exact hmove i hi (c₂.injective ((hρ i).symm.trans (hρfix _ hi₂)))

theorem hdisj_five (hS : CSetting 3 IH Ω K J) {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) 5}
    (D : PairChart Ω K J I) {c₁ c₂ : Fin 5 ↪ Fin (5 + 2)}
    (hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c)
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ) c₁)
    (hZ₂ : D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (5 + 2)))ᶜ ⊆
      conjSub D.t '' centMembers Ω D.u)
    (hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin 5)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e') :
    ∀ i : Fin 5, c₁ i ∈ D.γ.map D.ι → c₂ i ∉ D.γ.map D.ι := fun i hi =>
  hmove_five hS D hc₁ h₁ hZ₂ hcorr i (Finset.map_subset_map.mpr (Finset.subset_univ _) hi)

theorem hmove_five_of_eq {n : ℕ} (hn : n = 5) (hS : CSetting 3 IH Ω K J)
    {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} (D : PairChart Ω K J I) {c₁ c₂ : Fin n ↪ Fin (n + 2)}
    (hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c)
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2)))ᶜ) c₁)
    (hZ₂ : D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2)))ᶜ ⊆
      conjSub D.t '' centMembers Ω D.u)
    (hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e') :
    ∀ i : Fin n, c₁ i ∈ Finset.univ.map D.ι → c₂ i ∉ D.γ.map D.ι := by
  subst hn
  exact hmove_five hS D hc₁ h₁ hZ₂ hcorr

theorem hdisj_five_of_eq {n : ℕ} (hn : n = 5) (hS : CSetting 3 IH Ω K J)
    {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} (D : PairChart Ω K J I) {c₁ c₂ : Fin n ↪ Fin (n + 2)}
    (hc₁ : ∀ x, x ∈ Set.range c₁ ↔ x ≠ D.ι D.a ∧ x ≠ D.ι D.c)
    (h₁ : SubHyp D.IY (D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2)))ᶜ) c₁)
    (hZ₂ : D.IY.over ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2)))ᶜ ⊆
      conjSub D.t '' centMembers Ω D.u)
    (hcorr : ∀ M ∈ centMembers Ω D.u, ∀ (α : Finset (Fin n)) (hα : (α.map c₁).card = 4)
      (e : Bool), (M.subgroupOf (pSpan (centMembers Ω D.u))).map D.IY.φ = memBar (α.map c₁) hα e →
      ∃ (hα' : (α.map c₂).card = 4) (e' : Bool),
        (M.subgroupOf (pSpan (conjSub D.t '' centMembers Ω D.u))).map (D.IY.conjE D.t).φ =
          memBar (α.map c₂) hα' e') :
    ∀ i : Fin n, c₁ i ∈ D.γ.map D.ι → c₂ i ∉ D.γ.map D.ι := by
  subst hn
  exact hdisj_five hS D hc₁ h₁ hZ₂ hcorr

end Main

end CFSG.ClassicalInvolution.Q3.TC.Thin
