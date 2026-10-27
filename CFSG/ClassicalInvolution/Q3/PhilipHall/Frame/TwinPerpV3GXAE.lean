module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MLab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Base
public import Certificates.Certificate397301
public import CFSG.ClassicalInvolution.Q3.TL3T37

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

section AE

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {m : ℕ}

structure AEData (Φ : Set (Subgroup X)) (m : ℕ) where
  f : X →* AEQ m
  range_eq : f.range = TL4.aeModel m
  ker_le : f.ker ≤ Subgroup.center X
  label : ∀ L ∈ Φ, ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), L.map f = memBar α h b
  eq_of_map : ∀ K ∈ Φ, ∀ J ∈ Φ, K.map f = J.map f → K = J
  zlab : ∀ K ∈ Φ, ∀ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), K.map f = memBar α h b →
    ∀ z : X, IsUniqueInvolution K z → f z = zBar α h

theorem aeData_of_aeIdent (hm : 5 ≤ m) (hS : Q8Section X Φ) (I : AEIdent Φ m) :
    Nonempty (AEData Φ m) := by
  classical
  obtain ⟨I'⟩ := TL4.nonempty_aeIdentOn_of_aeIdent (P := Φ) (m := m) ⟨I⟩
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  obtain ⟨f, hrange, hker, hfx, hmap⟩ := aeIdentOn_toHom' hgen I'
  have hlab : ∀ L ∈ Φ, ∃ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool),
      L.map f = memBar α h b := by
    intro L hL
    obtain ⟨α, -, h, b, hl⟩ := I'.label L hL
    exact ⟨α, h, b, (hmap L hL).symm.trans hl⟩
  have h2 : ∀ L ∈ Φ, IsPGroup 2 ↥L := members_two_f hm hS f hker hlab
  have h8 : ∀ L ∈ Φ, Nat.card ↥L = 8 := by
    intro L hL
    obtain ⟨e⟩ := hS.q8 L hL L (TL4.Vtx.isSylow2In_self (h2 L hL))
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hmem : ∀ x : X, x ∈ pSpan Φ := fun x => hgen ▸ Subgroup.mem_top x
  have hz : ∀ K ∈ Φ, ∀ (α : Finset (Fin m)) (h : α.card = 4) (b : Bool), K.map f = memBar α h b →
      ∀ z : X, IsUniqueInvolution K z → f z = zBar α h := by
    intro K hK α h b hl z hzK
    have hlK : (K.subgroupOf (pSpan Φ)).map I'.φ = memBar α h b := (hmap K hK).trans hl
    rw [hfx]
    exact phi_map_eq_zBar I'.φ hm hK (h8 K hK) hlK hzK
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := by
    intro J hJ
    rw [eq_bot_iff]
    rintro x ⟨hxJ, hxk⟩
    obtain ⟨α, h, b, hl⟩ := hlab J hJ
    have hlJ : (J.subgroupOf (pSpan Φ)).map I'.φ = memBar α h b := (hmap J hJ).trans hl
    have hx1 : f x = f 1 := by rw [map_one]; exact hxk
    rw [hfx, hfx] at hx1
    have := phi_injOn I'.φ hm hJ (h8 J hJ) hlJ hxJ J.one_mem hx1
    exact this
  have hc := TwinDisc.ExitE4.centQuotGen hS.hyp h2 hker hmeet
  refine ⟨⟨f, hrange, hker, hlab, ?_, hz⟩⟩
  intro K hK J hJ h
  apply hc.eq_of_map K hK J hJ
  have hcomp : (QuotientGroup.kerLift f).comp (QuotientGroup.mk' f.ker) = f :=
    MonoidHom.ext fun x => rfl
  have hk : ∀ L : Subgroup X, L.map f =
      (L.map (QuotientGroup.mk' f.ker)).map (QuotientGroup.kerLift f) := fun L => by
    rw [Subgroup.map_map, hcomp]
  rw [hk K, hk J] at h
  exact Subgroup.map_injective (QuotientGroup.kerLift_injective f) h

theorem ae_involution_eq (hm : 5 ≤ m) (hm8 : m ≠ 8) (D : AEData Φ m) {P P' : Subgroup X} {p : X}
    (hP : P ∈ Φ) (hP' : P' ∈ Φ) (hPP' : P ≠ P') (hzP : IsUniqueInvolution P p)
    (hzP' : IsUniqueInvolution P' p) {M : Subgroup X} {w : X} (hM : M ∈ Φ)
    (hw : IsUniqueInvolution M w) (h : D.f w = D.f p) : w = p := by
  obtain ⟨α, hα, b, hb⟩ := D.label P hP
  obtain ⟨α', hα', b', hb'⟩ := D.label P' hP'
  obtain ⟨γ, hγ, c, hc⟩ := D.label M hM
  have e1 : zBar α hα = zBar α' hα' :=
    (D.zlab P hP α hα b hb p hzP).symm.trans (D.zlab P' hP' α' hα' b' hb' p hzP')
  have hαα' : α = α' := AE.eq_of_zBar_eq hm8 e1
  subst hαα'
  have e2 : zBar γ hγ = zBar α hα :=
    (D.zlab M hM γ hγ c hc w hw).symm.trans (h.trans (D.zlab P hP α hα b hb p hzP))
  have hγα : γ = α := AE.eq_of_zBar_eq hm8 e2
  subst hγα
  have hbb' : b ≠ b' := by
    intro hbb
    subst hbb
    exact hPP' (D.eq_of_map P hP P' hP' (hb.trans hb'.symm))
  by_cases hcb : c = b
  · subst hcb
    have hMP : M = P := D.eq_of_map M hM P hP (hc.trans hb.symm)
    subst hMP
    exact hw.eq hzP
  · have hcb' : c = b' := by
      cases c <;> cases b <;> cases b' <;> simp_all
    subst hcb'
    have hMP : M = P' := D.eq_of_map M hM P' hP' (hc.trans hb'.symm)
    subst hMP
    exact hw.eq hzP'

theorem ae_mem_centralizer (hm : 5 ≤ m) (hm8 : m ≠ 8) (hΩ : HypOmegaGen Φ) (D : AEData Φ m)
    {P P' : Subgroup X} {p : X} (hP : P ∈ Φ) (hP' : P' ∈ Φ) (hPP' : P ≠ P')
    (hzP : IsUniqueInvolution P p) (hzP' : IsUniqueInvolution P' p) {g : X}
    (hg : D.f g * D.f p = D.f p * D.f g) : g ∈ Subgroup.centralizer ({p} : Set X) := by
  have h1 : D.f (g * p * g⁻¹) = D.f p := by
    rw [map_mul, map_mul, map_inv, hg]
    group
  have h2 : g * p * g⁻¹ = p :=
    ae_involution_eq hm hm8 D hP hP' hPP' hzP hzP' (hΩ.conjInvariant g P hP) (hzP.conj g) h1
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc g * p = (g * p * g⁻¹) * g := by group
    _ = p * g := by rw [h2]

theorem ofPerm_conj_zBar (σ : Equiv.Perm (Fin m)) {γ : Finset (Fin m)} (h : γ.card = 4)
    (h' : (γ.image σ).card = 4) :
    mkQ m (ofPerm σ) * zBar γ h * (mkQ m (ofPerm σ))⁻¹ = zBar (γ.image σ) h' := by
  unfold zBar
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [ofPerm_conj_vec, zOf_vec_apply, zOf_vec_apply]
    have hr₁ : Set.range (emb γ h) = (↑γ : Set (Fin m)) := range_emb γ h
    have hr₂ : Set.range (emb (γ.image σ) h') = (↑(γ.image σ) : Set (Fin m)) := range_emb _ h'
    by_cases hx : x ∈ γ.image σ
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have h1 : σ.symm x ∈ Set.range (emb γ h) := by
        rw [hr₁, ← hyx]
        simpa using hy
      have h2 : x ∈ Set.range (emb (γ.image σ) h') := by rw [hr₂]; exact hx
      rw [if_pos h1, if_pos h2]
    · have h1 : σ.symm x ∉ Set.range (emb γ h) := by
        intro hmem
        rw [hr₁] at hmem
        exact hx (Finset.mem_image.mpr ⟨σ.symm x, hmem, by simp⟩)
      have h2 : x ∉ Set.range (emb (γ.image σ) h') := by rw [hr₂]; exact hx
      rw [if_neg h1, if_neg h2]
  · rw [ofPerm_conj_perm, zOf_perm, zOf_perm]
    simp

theorem ofPerm_mem_aeSub (σ : Equiv.Perm (Fin m)) (hσ : Equiv.Perm.sign σ = 1) :
    ofPerm σ ∈ aeSub m := by
  refine ⟨?_, hσ⟩
  show ∑ i, ((0 : Fin m → ZMod 2) i) = 0
  simp

theorem exists_lift_perm (D : AEData Φ m) (σ : Equiv.Perm (Fin m)) (hσ : Equiv.Perm.sign σ = 1) :
    ∃ c : X, D.f c = mkQ m (ofPerm σ) := by
  have : mkQ m (ofPerm σ) ∈ D.f.range := by
    rw [D.range_eq]
    exact ⟨ofPerm σ, ofPerm_mem_aeSub σ hσ, rfl⟩
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

theorem reach_sound (hm : 5 ≤ m) (hm8 : m ≠ 8) (hΩ : HypOmegaGen Φ) (D : AEData Φ m)
    {A A' B B' : Subgroup X} {z τ : X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ) (hB' : B' ∈ Φ)
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z)
    (hτB : IsUniqueInvolution B τ) (hτB' : IsUniqueInvolution B' τ)
    {α β : Finset (Fin m)} (hα : α.card = 4) (hβ : β.card = 4)
    (hfz : D.f z = zBar α hα) (hfτ : D.f τ = zBar β hβ) (k : ℕ) :
    ∀ γ ∈ Certificates.AEOrbit.reach m α β k, ∃ (hγ : γ.card = 4) (h : X),
      h ∈ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) ∧
        D.f (h * z * h⁻¹) = zBar γ hγ := by
  induction k with
  | zero =>
    intro γ hγ
    have : γ = α := by simpa [Certificates.AEOrbit.reach] using hγ
    subst this
    exact ⟨hα, 1, one_mem _, by simp [hfz]⟩
  | succ k ih =>
    intro γ hγ
    simp only [Certificates.AEOrbit.reach, Certificates.AEOrbit.step, Finset.mem_union,
      Finset.mem_biUnion, List.mem_toFinset, List.mem_map] at hγ
    rcases hγ with hγ | ⟨γ', hγ', σ, hσ, rfl⟩
    · exact ih γ hγ
    · obtain ⟨hγ'4, h', hh', hf'⟩ := ih γ' hγ'
      have hcard : (γ'.image σ).card = 4 := by
        rw [Finset.card_image_of_injective _ σ.injective]; exact hγ'4
      refine ⟨hcard, ?_⟩
      rw [List.mem_append] at hσ
      rcases hσ with hσ | hσ
      · obtain ⟨-, hσ'⟩ := List.mem_filter.mp hσ
        simp only [decide_eq_true_eq] at hσ'
        obtain ⟨hsign, himg⟩ := hσ'
        obtain ⟨c, hc⟩ := exists_lift_perm D σ hsign
        have hc4 : (α.image σ).card = 4 := by rw [himg]; exact hα
        have hconj : D.f c * D.f z = D.f z * D.f c := by
          rw [hc, hfz]
          have := ofPerm_conj_zBar σ hα hc4
          rw [zBar_congr himg hc4 hα] at this
          calc mkQ m (ofPerm σ) * zBar α hα
              = (mkQ m (ofPerm σ) * zBar α hα * (mkQ m (ofPerm σ))⁻¹) * mkQ m (ofPerm σ) := by
                group
            _ = zBar α hα * mkQ m (ofPerm σ) := by rw [this]
        have hcC : c ∈ Subgroup.centralizer ({z} : Set X) :=
          ae_mem_centralizer hm hm8 hΩ D hA hA' hAA' hzA hzA' hconj
        refine ⟨c * h', Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC) hh', ?_⟩
        calc D.f (c * h' * z * (c * h')⁻¹) = D.f c * D.f (h' * z * h'⁻¹) * (D.f c)⁻¹ := by
              rw [show c * h' * z * (c * h')⁻¹ = c * (h' * z * h'⁻¹) * c⁻¹ by group, map_mul,
                map_mul, map_inv]
          _ = zBar (γ'.image σ) hcard := by
              rw [hf', hc]
              exact ofPerm_conj_zBar σ hγ'4 hcard
      · obtain ⟨-, hσ'⟩ := List.mem_filter.mp hσ
        simp only [decide_eq_true_eq] at hσ'
        obtain ⟨hsign, himg⟩ := hσ'
        obtain ⟨c, hc⟩ := exists_lift_perm D σ hsign
        have hc4 : (β.image σ).card = 4 := by rw [himg]; exact hβ
        have hconj : D.f c * D.f τ = D.f τ * D.f c := by
          rw [hc, hfτ]
          have := ofPerm_conj_zBar σ hβ hc4
          rw [zBar_congr himg hc4 hβ] at this
          calc mkQ m (ofPerm σ) * zBar β hβ
              = (mkQ m (ofPerm σ) * zBar β hβ * (mkQ m (ofPerm σ))⁻¹) * mkQ m (ofPerm σ) := by
                group
            _ = zBar β hβ * mkQ m (ofPerm σ) := by rw [this]
        have hcC : c ∈ Subgroup.centralizer ({τ} : Set X) :=
          ae_mem_centralizer hm hm8 hΩ D hB hB' hBB' hτB hτB' hconj
        refine ⟨c * h', Subgroup.mul_mem _ (Subgroup.mem_sup_right hcC) hh', ?_⟩
        calc D.f (c * h' * z * (c * h')⁻¹) = D.f c * D.f (h' * z * h'⁻¹) * (D.f c)⁻¹ := by
              rw [show c * h' * z * (c * h')⁻¹ = c * (h' * z * h'⁻¹) * c⁻¹ by group, map_mul,
                map_mul, map_inv]
          _ = zBar (γ'.image σ) hcard := by
              rw [hf', hc]
              exact ofPerm_conj_zBar σ hγ'4 hcard

theorem gen_of_aeIdent (hm : m = 5 ∨ m = 6) (hS : Q8Section X Φ)
    (I : AEIdent Φ m) {A A' B B' : Subgroup X} {z τ : X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hB : B ∈ Φ)
    (hB' : B' ∈ Φ) (hAA' : A ≠ A') (hBB' : B ≠ B') (hzA : IsUniqueInvolution A z)
    (hzA' : IsUniqueInvolution A' z) (hτB : IsUniqueInvolution B τ)
    (hτB' : IsUniqueInvolution B' τ) (hτz : τ ≠ z) :
    ∀ g : X, g ∈ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) := by
  have hm5 : 5 ≤ m := by omega
  have hm8 : m ≠ 8 := by omega
  obtain ⟨D⟩ := aeData_of_aeIdent hm5 hS I
  have hΩ := hS.hyp
  obtain ⟨α, hα, b, hb⟩ := D.label A hA
  obtain ⟨β, hβ, c, hc⟩ := D.label B hB
  have hfz : D.f z = zBar α hα := D.zlab A hA α hα b hb z hzA
  have hfτ : D.f τ = zBar β hβ := D.zlab B hB β hβ c hc τ hτB
  have hαβ : α ≠ β := by
    intro h
    subst h
    exact hτz (ae_involution_eq hm5 hm8 D hA hA' hAA' hzA hzA' hB hτB (hfτ.trans hfz.symm))
  have hαm : α ∈ Certificates.AEOrbit.fours m :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hα⟩
  have hβm : β ∈ Certificates.AEOrbit.fours m :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hβ⟩
  have hall : Certificates.AEOrbit.reach m α β 4 = Certificates.AEOrbit.fours m := by
    have hcert := Certificates.certificate397301
    unfold Certificates.AEOrbit.check at hcert
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcert
    rcases hm with rfl | rfl
    · exact hcert.1 α hαm β hβm hαβ
    · exact hcert.2 α hαm β hβm hαβ
  intro g
  obtain ⟨γ, hγ, c', hc'⟩ := D.label (conjSub g A) (hΩ.conjInvariant g A hA)
  have hfg : D.f (g * z * g⁻¹) = zBar γ hγ :=
    D.zlab _ (hΩ.conjInvariant g A hA) γ hγ c' hc' _ (hzA.conj g)
  have hγm : γ ∈ Certificates.AEOrbit.reach m α β 4 := by
    rw [hall]
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hγ⟩
  obtain ⟨hγ', h, hh, hfh⟩ := reach_sound hm5 hm8 hΩ D hA hA' hB hB' hAA' hBB' hzA hzA' hτB hτB'
    hα hβ hfz hfτ 4 γ hγm
  have e : D.f (h * z * h⁻¹) = D.f (g * z * g⁻¹) := hfh.trans hfg.symm
  simp only [map_mul, map_inv] at e
  have hw : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set X) := by
    refine ae_mem_centralizer hm5 hm8 hΩ D hA hA' hAA' hzA hzA' ?_
    rw [map_mul, map_inv]
    calc (D.f h)⁻¹ * D.f g * D.f z
        = (D.f h)⁻¹ * (D.f g * D.f z * (D.f g)⁻¹) * D.f g := by group
      _ = (D.f h)⁻¹ * (D.f h * D.f z * (D.f h)⁻¹) * D.f g := by rw [e]
      _ = D.f z * ((D.f h)⁻¹ * D.f g) := by group
  have hg : g = h * (h⁻¹ * g) := by group
  rw [hg]
  exact Subgroup.mul_mem _ hh (Subgroup.mem_sup_left hw)

end AE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX
