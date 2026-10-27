module

public import CFSG.Certificates.Kernel.S1277KSvCover
public import CFSG.Certificates.Kernel.S1277KFrSound

public section

namespace CFSG.KS.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Gm
  CFSG.KC.S1277Sv CFSG.KC.S1277Fr CFSG.KC.Enum CFSG.KS.S1277Lat CFSG.KS.S1277Mod
  CFSG.KS.S1277Sig CFSG.KS.S1277Gm CFSG.KS.S1277Cand CFSG.KS.S1277Fr CFSG.Quasithin.H13.I1277
  Certificates.Data.S1277Surv Certificates.Data.S1277Sig

theorem pk_eq_packQ (σ : Equiv.Perm (Fin (2 ^ 6))) :
    pk σ = packQ fun i => (colsOf σ).getD i 0 := by
  rw [pk_def]
  have hl := length_colsOf σ
  generalize colsOf σ = l at hl ⊢
  match l, hl with
  | [a, b, c, d, e, f], _ => simp [packC, packQ]

theorem packQ_congr {f g : ℕ → ℕ} (h : ∀ i < 6, f i = g i) : packQ f = packQ g := by
  simp only [packQ]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num)]

section Gens

variable {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {M : Mdl} {κ : G → ℕ}

theorem sgChk_mem (hκ : MCod K M κ) (hKH : K ≤ H) (hQK : Q ≤ K) {m : ℕ}
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ m.testBit n = true) {gs ts : List ℕ} {p TP : ℕ}
    {pg pr pt ws : List ℕ} (hfr : frChk M m gs ts p pg pr pt TP 6 ws = true)
    (D : FrData H Q (Phi' Q) 6) (hD : ∀ x, D.wc x = rd6 TP (κ x)) {kt kg sg : List ℕ}
    (hgen : genChk M kg kt = true) (h : sgChk M kg TP ws sg = true) :
    ∀ y ∈ sg, pkSet D.rho.range y := by
  rw [frChk] at hfr
  simp only [Bool.and_eq_true] at hfr
  have hws := hfr.2
  rw [sgChk, Bool.and_eq_true] at h
  obtain ⟨hlen, hsg⟩ := h
  have hlen' := Nat.eq_of_beq_eq_true hlen
  rw [genChk, Bool.and_eq_true] at hgen
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hj' : j < kg.length := by omega
  have hkl : kg.getD j 0 < M.nb * 64 := by
    have := (allL_iff.1 hgen.1) _ (List.getElem_mem hj')
    rw [Nat.blt_eq] at this
    rwa [List.getD_eq_getElem _ _ hj']
  obtain ⟨k, hk, hκk⟩ := hκ.surj _ hkl
  refine ⟨D.rho ⟨k, hKH hk⟩, ⟨_, rfl⟩, ?_⟩
  have hc := Nat.eq_of_beq_eq_true ((allL_iff.1 hsg) j (List.mem_range.2 hj'))
  rw [List.getD_eq_getElem _ _ hj] at hc
  rw [hc, pk_eq_packQ]
  refine packQ_congr fun i hi => ?_
  have hi2 : 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
  have hw := (allL_iff.1 hws) (2 ^ i) (List.mem_range.2 hi2)
  rw [Bool.and_eq_true] at hw
  obtain ⟨q, hq, hqκ⟩ := (hQN _).2 hw.1
  have hwq : D.wc q = 2 ^ i := by rw [hD, hqκ]; exact Nat.eq_of_beq_eq_true hw.2
  rw [List.getD_eq_getElem _ _ (by rw [length_colsOf]; exact hi), getElem_colsOf _ i hi]
  have h3 := D.rho_of_mem ⟨k, hKH hk⟩ hq
  have e : (⟨D.wc q, D.wc_lt q hq⟩ : Fin (2 ^ 6)) = ⟨2 ^ i, hi2⟩ := Fin.ext hwq
  rw [e] at h3
  rw [h3, hD, hκ.mul _ (K.mul_mem hk (hQK hq)) _ (K.inv_mem hk), hκ.mul _ hk _ (hQK hq),
    hκ.inv _ hk, hκk, hqκ]
  rfl

end Gens

section R

variable {L : ℕ} {R : Subgroup (Equiv.Perm (Fin (2 ^ 6)))}

theorem tyL_zero (sl a1 a2 : List ℕ) : tyL 0 sl a1 a2 = sl := rfl

theorem tyL_two (sl a1 a2 : List ℕ) : tyL 2 sl a1 a2 = a1 := rfl

theorem tyL_three (sl a1 a2 : List ℕ) : tyL 3 sl a1 a2 = a2 := rfl

theorem mid_mem (hR : R ≤ Sig 6 (φL L)) {a b g : ℕ} (ha : pkSet R a) (hb : pkSet R b)
    (hg : pkSet (Sig 6 (φL L)) g) (h : pkSet R (mulQ a (mulQ g b))) : pkSet R g := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨ρ, hρ, he⟩ := h
  rw [mulQ_eq, mulQ_eq, ← pk_mul hγ.1, ← pk_mul (hR hα).1] at he
  have hρ' : ρ = α * (γ * β) := pk_injective (hR hρ)
    ((Sig 6 (φL L)).mul_mem (hR hα) ((Sig 6 (φL L)).mul_mem hγ (hR hβ))) he
  refine ⟨γ, ?_, rfl⟩
  have e : γ = α⁻¹ * ρ * β⁻¹ := by rw [hρ']; group
  rw [e]
  exact R.mul_mem (R.mul_mem (R.inv_mem hα) hρ) (R.inv_mem hβ)

theorem pkSet_append {l l' : List ℕ} (h : ∀ g ∈ l, pkSet R g) (h' : ∀ g ∈ l', pkSet R g) :
    ∀ g ∈ l ++ l', pkSet R g := fun g hg => (List.mem_append.1 hg).elim (h g) (h' g)

theorem surv_R (hR : R ≤ Sig 6 (φL L)) {m : ℕ} (hRc : Nat.card R = 24 * m) (hm : ¬ 2 ∣ m)
    (hm1 : m ≠ 1) {sg sl sp sj sd pl pi vg : List ℕ} {sp36 hp vt k1 k2 : ℕ}
    {vw w1 : List (List ℕ)} {a1 a1p a1j a1d a2 a2p a2j a2d : List ℕ}
    {vr : List (List ℕ)} {vb : List ℕ}
    (hsg : ∀ g ∈ sg, pkSet R g) (hsll : sl.length = 24) (hsli : incL 0 sl = true)
    (hslt : treeQ sl sp sj sd sg = true) (hpc : pChk sl pl pi = true)
    (hvg : vgChk L [] vg = true) (hhp : hpChk vg sl sp36 hp = true)
    (hcnt : cntChk vr vb = true) (hvr : vr.length = 40)
    (hcov : ∀ c < 40, covChk sp36 hp vt sl a1 a2 vr vb c = true)
    (hsig : Nat.card (Sig 6 (φL L)) = 40320)
    (hwS : allLt 130 (wSChk pl sg vg vt vw) = true)
    (hwA1 : allLt 130 (wAChk pl sg vg vt k1 2 w1) = true)
    (ha1 : aChk1 sg sl vg vt k1 2 a1 a1p a1j a1d = true)
    (ha2 : aChk1 sg sl vg vt k2 3 a2 a2p a2j a2d = true) :
    (∀ y, pkSet R y ↔ y ∈ a1) ∨ (∀ y, pkSet R y ↔ y ∈ a2) := by
  classical
  have h16 : ¬ 16 ∣ Nat.card R := by
    rw [hRc]
    omega
  have hslR : ∀ y ∈ sl, pkSet R y := treeQ_mem hR hslt hsg
  have hplR : ∀ y ∈ pl, pkSet R y := by
    intro y hy
    rw [pChk] at hpc
    simp only [Bool.and_eq_true] at hpc
    exact hslR y (memL_iff.1 ((allL_iff.1 hpc.2) y hy))
  have hslS : ∀ y ∈ sl, pkSet (Sig 6 (φL L)) y := fun y hy => by
    obtain ⟨σ, hσ, rfl⟩ := hslR y hy
    exact ⟨σ, hR hσ, rfl⟩
  obtain ⟨hvgl, hvgS⟩ := vgChk_spec hvg
  have hcv := cover_sound hslS hsll hvg hhp hcnt hvr hcov hsig
  rw [aChk1] at ha1 ha2
  simp only [Bool.and_eq_true, Nat.blt_eq] at ha1 ha2
  obtain ⟨⟨⟨⟨⟨⟨hk1, ht1⟩, hu1⟩, -⟩, -⟩, hT1⟩, hs1⟩ := ha1
  obtain ⟨⟨⟨⟨⟨⟨hk2, ht2⟩, hu2⟩, -⟩, -⟩, hT2⟩, hs2⟩ := ha2
  have ht1' := Nat.eq_of_beq_eq_true ht1
  have ht2' := Nat.eq_of_beq_eq_true ht2
  have huniq : ∀ k < 130, ∀ (ty ki : ℕ),
      allLt 130 (fun k => !Nat.beq (rd2 vt k) ty || Nat.beq k ki) = true →
      rd2 vt k = ty → k = ki := by
    intro k hk ty ki hu hty
    have := (allLt_iff.1 hu) k hk
    rw [hty, Bool.or_eq_true] at this
    rcases this with h | h
    · exact absurd h (by simp)
    · exact Nat.eq_of_beq_eq_true h
  have hvgk : ∀ k < 130, vg.getD k 0 ∈ vg := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hsplit : ∀ σ ∈ R, pk σ ∈ sl ∨ (pk σ ∈ a1 ∧ pkSet R (vg.getD k1 0)) ∨
      (pk σ ∈ a2 ∧ pkSet R (vg.getD k2 0)) := by
    intro σ hσ
    obtain ⟨r, hr, he, hty⟩ := hcv σ (hR hσ)
    have hk : r / 576 < 130 := by omega
    have hmid : pkSet R (vg.getD (r / 576) 0) :=
      mid_mem hR (hslR _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))
        (hslR _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))
        (hvgS _ (hvgk _ hk)) ⟨σ, hσ, he⟩
    have h4 : rd2 vt (r / 576) < 4 := Nat.mod_lt _ (by norm_num)
    obtain h | h | h | h : rd2 vt (r / 576) = 0 ∨ rd2 vt (r / 576) = 1 ∨ rd2 vt (r / 576) = 2 ∨
        rd2 vt (r / 576) = 3 := by omega
    · rw [h, tyL_zero] at hty
      exact Or.inl (hty.resolve_left (by norm_num))
    · exfalso
      have hw := (allLt_iff.1 hwS) _ hk
      rw [wSChk, h, Bool.or_eq_true] at hw
      rcases hw with hw | hw
      · exact absurd hw (by decide)
      · exact not_witQ hR hplR hpc h16
          (pkSet_append hsg fun g hg => by rw [List.mem_singleton.1 hg]; exact hmid) hw
    · rw [h, tyL_two] at hty
      rw [← huniq _ hk 2 k1 hu1 h]
      exact Or.inr (Or.inl ⟨hty.resolve_left (by norm_num), hmid⟩)
    · rw [h, tyL_three] at hty
      rw [← huniq _ hk 3 k2 hu2 h]
      exact Or.inr (Or.inr ⟨hty.resolve_left (by norm_num), hmid⟩)
  have hA : ∀ (k : ℕ) (a ap aj ad : List ℕ), treeQ a ap aj ad (sg ++ [vg.getD k 0]) = true →
      pkSet R (vg.getD k 0) → ∀ y ∈ a, pkSet R y := fun k a ap aj ad hT hk =>
    treeQ_mem hR hT (pkSet_append hsg fun g hg => by rw [List.mem_singleton.1 hg]; exact hk)
  have hsa1 : ∀ y ∈ sl, y ∈ a1 := fun y hy => memL_iff.1 ((allL_iff.1 hs1) y hy)
  have hsa2 : ∀ y ∈ sl, y ∈ a2 := fun y hy => memL_iff.1 ((allL_iff.1 hs2) y hy)
  by_cases hR1 : pkSet R (vg.getD k1 0)
  · by_cases hR2 : pkSet R (vg.getD k2 0)
    · exfalso
      have hw := (allLt_iff.1 hwA1) k2 hk2
      rw [wAChk, ht2', Bool.or_eq_true, Bool.or_eq_true] at hw
      rcases hw with (hw | hw) | hw
      · exact absurd hw (by decide)
      · exact absurd hw (by decide)
      · refine not_witQ hR hplR hpc h16 (pkSet_append hsg fun g hg => ?_) hw
        rcases List.mem_cons.1 hg with rfl | hg
        · exact hR1
        · rw [List.mem_singleton.1 hg]; exact hR2
    · left
      intro y
      refine ⟨fun hy => ?_, fun hy => hA k1 a1 a1p a1j a1d hT1 hR1 y hy⟩
      obtain ⟨σ, hσ, rfl⟩ := hy
      rcases hsplit σ hσ with h | h | h
      · exact hsa1 _ h
      · exact h.1
      · exact absurd h.2 hR2
  · by_cases hR2 : pkSet R (vg.getD k2 0)
    · right
      intro y
      refine ⟨fun hy => ?_, fun hy => hA k2 a2 a2p a2j a2d hT2 hR2 y hy⟩
      obtain ⟨σ, hσ, rfl⟩ := hy
      rcases hsplit σ hσ with h | h | h
      · exact hsa2 _ h
      · exact absurd h.2 hR1
      · exact h.1
    · exfalso
      have hiff : ∀ y, pkSet R y ↔ y ∈ sl := by
        intro y
        refine ⟨fun hy => ?_, fun hy => hslR y hy⟩
        obtain ⟨σ, hσ, rfl⟩ := hy
        rcases hsplit σ hσ with h | h | h
        · exact h
        · exact absurd h.2 hR1
        · exact absurd h.2 hR2
      have := card_range_eq_of_pkSet hR (incL_nodup sl 0 hsli).2 hiff
      rw [hRc, hsll] at this
      omega

end R

end CFSG.KS.S1277Sv

end
