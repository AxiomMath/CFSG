module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf12Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWAe5Sylow
public import CFSG.ClassicalInvolution.Q3.AE.Conj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.Ae5Mod

section Psi

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem psi_map_eq (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) (L : Subgroup Y) :
    L.map (psiOfF F I) = (L.subgroupOf (pSpan Δ)).map I.φ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, F.gen ▸ Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  · rintro ⟨⟨y, hy'⟩, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem psi_label (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) {L : Subgroup Y} (hL : L ∈ Δ) :
    ∃ (p : Fin 5) (b : Bool), L.map (psiOfF F I) = AE.memBar (miss p) (card_miss p) b := by
  obtain ⟨α, h, b, hl⟩ := I.label L hL
  obtain ⟨p, rfl⟩ := exists_miss h
  exact ⟨p, b, by rw [psi_map_eq]; exact hl⟩

theorem psi_inj (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) {L M : Subgroup Y} (hL : L ∈ Δ)
    (hM : M ∈ Δ) (hLM : L.map (psiOfF F I) = M.map (psiOfF F I)) : L = M := by
  obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
  refine TwinDisc.ExitO2.fam_eq_of_phi_mem I.φ F (le_refl 5) I.ker_le I.label hL hM haL ha2 ?_
  have := I.mem_map hL haL
  rw [← psi_map_eq F I, hLM, psi_map_eq F I] at this
  exact this

theorem psi_zimg (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) {L : Subgroup Y} (hL : L ∈ Δ)
    {p : Fin 5} {b : Bool} (hl : L.map (psiOfF F I) = AE.memBar (miss p) (card_miss p) b) {u : Y}
    (hu : IsUniqueInvolution L u) : psiOfF F I u = AE.zBar (miss p) (card_miss p) := by
  have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
  exact I.map_eq_zBar (le_refl 5) hL h8 (by rw [← psi_map_eq]; exact hl) hu

theorem psi_point_unique (F : TwinDisc.ExitO2.Q8Fam Y Δ) (I : AEIdent Δ 5) {L : Subgroup Y}
    (hL : L ∈ Δ) {p q : Fin 5} {b c : Bool}
    (hp : L.map (psiOfF F I) = AE.memBar (miss p) (card_miss p) b)
    (hq : L.map (psiOfF F I) = AE.memBar (miss q) (card_miss q) c) {u : Y}
    (hu : IsUniqueInvolution L u) : p = q :=
  miss_inj (AE.eq_of_zBar_eq (by norm_num)
    ((psi_zimg F I hL hp hu).symm.trans (psi_zimg F I hL hq hu)))

end Psi

theorem map_conj_memKStar {n : ℕ} (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι) :
    (AE.memKStar ι).map (MulAut.conj (AE.twinVec ι j)).toMonoidHom = AE.memK ι := by
  have hee : AE.twinVec ι j * AE.twinVec ι j = 1 := AE.twinVec_mul_self ι j
  have hinv : (AE.twinVec ι j)⁻¹ = AE.twinVec ι j := inv_eq_of_mul_eq_one_right hee
  conv_lhs => rw [← AE.map_conj_memK ι hj]
  rw [Subgroup.map_map]
  convert Subgroup.map_id (AE.memK ι) using 2
  refine MonoidHom.ext fun x => ?_
  show AE.twinVec ι j * (AE.twinVec ι j * x * (AE.twinVec ι j)⁻¹) * (AE.twinVec ι j)⁻¹ = x
  rw [hinv, ← mul_assoc, ← mul_assoc, hee, one_mul, mul_assoc, hee, mul_one]

theorem map_conj_memBar_not {n : ℕ} (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι)
    (α : Finset (Fin n)) (h : α.card = 4) (hι : ι = AE.emb α h) (b : Bool) :
    (AE.memBar α h b).map (MulAut.conj (AE.mkQ n (AE.twinVec ι j))).toMonoidHom =
      AE.memBar α h (!b) := by
  subst hι
  cases b
  · show ((AE.memKStar (AE.emb α h)).map (AE.mkQ n)).map _ = (AE.memK (AE.emb α h)).map (AE.mkQ n)
    rw [Subgroup.map_map, ← map_conj_memKStar _ hj, Subgroup.map_map]
    congr 1
  · show ((AE.memK (AE.emb α h)).map (AE.mkQ n)).map _ = (AE.memKStar (AE.emb α h)).map (AE.mkQ n)
    rw [Subgroup.map_map, ← AE.map_conj_memK _ hj, Subgroup.map_map]
    congr 1

section Exit


variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem ae5ExitQ8_proved : AE5ExitQ8 := by
  intro G _ _ Ω K S R W H c F ⟨I⟩
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'tw
  obtain ⟨hRΩ, hRK, hRS⟩ := c.stand.hR
  obtain ⟨hW, hWS, hWn⟩ := c.stand.hW
  have hK := c.stand.mem
  have hRK' : R = K := by
    refine Subgroup.eq_of_le_of_card_ge hRK ?_
    rw [F.card K hK]
    exact Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hR'K'' : R' = K' := by
    refine Subgroup.eq_of_le_of_card_ge hR'K' ?_
    rw [F.card K' hK'Ω]
    exact Sec6Gen.eight_le_of_mem_RSet hΩ hR'
  have hKperp : K' ∈ KPerp Ω K := by
    refine Set.mem_insert_of_mem _ ⟨hK'Ω, hK'ne, R', hR', hR'K', fun x hx => ?_⟩
    exact hΩ.le_normalizer_of_twin hK'Ω hK hK'ne hzK' hzK (hR'K' hx)
  have hRR'2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  have hcomm' : Commutes R R' :=
    hΩ.commutes_of_twin_of_isPGroup hK hK'Ω (Ne.symm hK'ne) hzK hzK' hRK hR'K' hRR'2
  have hcommKK : Commutes K K' := by rw [← hRK', ← hR'K'']; exact hcomm'
  obtain ⟨x₀, hx₀, hx₀4, hx₀R⟩ := exists_order_four_inf_W hΩ hW hWS hK hRΩ hRK hRS
  have hKW : K ⊓ W ∈ USet Ω := inf_W_mem_USet' hΩ hW hWS hK hRΩ hRK hRS
  set ψ : G →* AE.AEQ 5 := psiOfF F I with hψdef
  obtain ⟨m, b, hKl⟩ := psi_label F I hK
  obtain ⟨m', b', hK'l⟩ := psi_label F I hK'Ω
  have hψz : ψ z = AE.zBar (miss m) (card_miss m) := psi_zimg F I hK hKl hzK
  have hψz' : ψ z = AE.zBar (miss m') (card_miss m') := psi_zimg F I hK'Ω hK'l hzK'
  obtain rfl : m = m' :=
    (miss_inj (AE.eq_of_zBar_eq (by norm_num) (hψz'.symm.trans hψz))).symm
  have hzne : ψ z ≠ 1 := by rw [hψz]; exact AE.zBar_ne_one (le_refl 5) _ _
  have hbb : b ≠ b' := by
    intro h
    subst h
    exact hK'ne (psi_inj F I hK'Ω hK (by rw [hKl, hK'l]))
  have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
  set ι := AE.emb (miss m) (card_miss m) with hι
  have hιrange : Set.range ι = ↑(miss m) := AE.range_emb _ _
  have hmι : m ∉ Set.range ι := by
    rw [hιrange]; simp [miss]
  set e := AE.twinVec ι m with he
  have he_ae : e ∈ AE.aeSub 5 := (AE.twinVec_mem ι hmι ⊤).1
  have he_ev : e ∈ evenVec 5 := mem_evenVec.mpr ⟨rfl, he_ae.1⟩
  have heR : AE.mkQ 5 e ∈ ψ.range := by
    have hmem : AE.mkQ 5 e ∈ I.φ.range := by
      rw [I.range_eq]; exact ⟨e, he_ae, rfl⟩
    obtain ⟨⟨y, hy⟩, hy'⟩ := hmem
    exact ⟨y, hy'⟩
  obtain ⟨s, hsS, hsψ⟩ := exists_mem_sylow_evenVec ψ S he_ev heR
  have hKs : conjSub s K = K' := by
    have hKsΩ : conjSub s K ∈ Ω := hΩ.conjInvariant s K hK
    refine psi_inj F I hKsΩ hK'Ω ?_
    have h1 : (conjSub s K).map ψ = (K.map ψ).map (MulAut.conj (ψ s)).toMonoidHom := by
      show (K.map (MulAut.conj s).toMonoidHom).map ψ = _
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun x => ?_
      simp [MulAut.conj_apply]
    rw [h1, hKl, hsψ, map_conj_memBar_not ι hmι (miss m) (card_miss m) hι b, hK'l, hb']
  set y₀ : G := s * x₀ * s⁻¹ with hy₀
  have hy₀K' : y₀ ∈ K' := by rw [← hKs]; exact conj_mem_conjSub hx₀.1
  have hy₀W : y₀ ∈ W := by
    have := conj_mem_conjSub (n := s) hx₀.2
    rwa [hWn s hsS] at this
  have hx₀sq : x₀ * x₀ = z := by
    have h4 : (x₀ * x₀) * (x₀ * x₀) = 1 := by
      have : x₀ ^ 4 = 1 := by rw [← hx₀4]; exact pow_orderOf_eq_one x₀
      calc (x₀ * x₀) * (x₀ * x₀) = x₀ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    rcases hzK.unique (x₀ * x₀) (K.mul_mem hx₀.1 hx₀.1) h4 with h | h
    · exfalso
      have : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx₀4] at this
      omega
    · exact h
  obtain ⟨k, hkmem, hkψ⟩ : ∃ k ∈ AE.kList ++ AE.kStarList, ψ x₀ = AE.mkQ 5 (AE.embed ι k) := by
    have hx₀m : ψ x₀ ∈ K.map ψ := ⟨x₀, hx₀.1, rfl⟩
    rw [hKl] at hx₀m
    obtain ⟨kh, hkh, hkhψ⟩ := hx₀m
    cases b
    · obtain ⟨k, hk, rfl⟩ : kh ∈ AE.memKStar ι := hkh
      exact ⟨k, List.mem_append_right _ hk, hkhψ.symm⟩
    · obtain ⟨k, hk, rfl⟩ : kh ∈ AE.memK ι := hkh
      exact ⟨k, List.mem_append_left _ hk, hkhψ.symm⟩
  have hzbar2 : AE.zBar (miss m) (card_miss m) * AE.zBar (miss m) (card_miss m) = 1 := by
    have : AE.zOf ι * AE.zOf ι = 1 := by
      have := mul_inv_cancel (AE.zOf ι)
      rwa [AE.zOf_inv] at this
    show AE.mkQ 5 (AE.zOf ι) * AE.mkQ 5 (AE.zOf ι) = 1
    rw [← map_mul, this, map_one]
  have hψsq : ψ x₀ * ψ x₀ = ψ z := by rw [← map_mul, hx₀sq]
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hzne
    rw [← hψsq, hkψ, map_one, map_one, one_mul]
  have hkz : k ≠ AE.zQ := by
    rintro rfl
    apply hzne
    rw [← hψsq, hkψ]
    exact hzbar2
  have hψy₀ : ψ y₀ = AE.mkQ 5 (AE.embed ι (e0 * k * e0)) := by
    have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (AE.twinVec_mul_self ι m)
    rw [hy₀, map_mul, map_mul, map_inv, hsψ, hkψ, ← map_inv, hinv, ← map_mul, ← map_mul]
    congr 1
    exact AE.twinVec_conj_embed ι hmι k
  have hψa : ψ (x₀ * y₀) = AE.mkQ 5 (AE.embed (permEmb ι (Classical.choose (e0Prod k hkmem hk1 hkz).2))
      w0) := by
    obtain ⟨hperm, hπ⟩ := e0Prod k hkmem hk1 hkz
    rw [embed_eq_embed_permEmb ι _ _ hperm (Classical.choose_spec hπ), map_mul, hkψ, hψy₀,
      ← map_mul, ← map_mul]
  obtain ⟨ha2, ha1, hgen⟩ := ae5Gen_of_prod G Ω F I K hK K' hK'Ω hK'ne z hzK hzK' hcommKK
    (permEmb ι (Classical.choose (e0Prod k hkmem hk1 hkz).2)) x₀ hx₀.1 y₀ hy₀K'
    (fun p b'' hl => by
      rw [range_permEmb, hιrange, psi_point_unique F I hK hKl hl hzK])
    hψa
  have haKK : x₀ * y₀ ∈ K ⊔ K' := Subgroup.mul_mem_sup hx₀.1 hy₀K'
  have haW : x₀ * y₀ ∈ W := W.mul_mem hx₀.2 hy₀W
  have hCa : Subgroup.centralizer ({x₀ * y₀} : Set G) ≤ H :=
    c.hyp.cent K hK hKW K' hKperp R R' hRΩ hRK hRS hR' hR'K' hR'S (Or.inl hcomm') (x₀ * y₀)
      (Subgroup.mul_mem_sup hx₀R (hR'K'' ▸ hy₀K')) haW ha1 ha2
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hzK
  apply c.proper
  rw [eq_top_iff, ← hgen]
  exact sup_le hCz hCa

end Exit

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
