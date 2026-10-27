module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem starCent_conj_comm {G : Type} [Group G] (φ : G ≃* G) {g x : G}
    (hφ2 : φ (φ x) = x) (hcomm : φ x * g = g * φ x) : x * φ g = φ g * x := by
  calc x * φ g = φ (φ x) * φ g := by rw [hφ2]
    _ = φ (φ x * g) := (map_mul φ _ _).symm
    _ = φ (g * φ x) := by rw [hcomm]
    _ = φ g * φ (φ x) := map_mul φ _ _
    _ = φ g * x := by rw [hφ2]

theorem s7_card_cent_derived {a z b c : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a)
    (hc : c ∈ sSet a z b 2) : Nat.card ↥(derivedOf (Gxy a b) ⊓ Gx c) = 720 := by
  classical
  have hc' : c ∈ sBase a b ∧ (a * c) ^ 2 = b := by simpa [sSet] using hc
  have hcsq : (a * c) ^ 2 = b := hc'.2
  have ha2 : a ^ 2 = 1 := s7_sq_of_isConj_a H (IsConj.refl a)
  have hb2 : b ^ 2 = 1 := s7_sq_of_isConj_a H hb.1
  have hc2 : c ^ 2 = 1 := s7_sq_of_isConj_a H hc'.1.1
  have ha1 : a ≠ 1 := s7_ne_one_of_isConj_a H (IsConj.refl a)
  have hb1 : b ≠ 1 := s7_ne_one_of_isConj_a H hb.1
  have hcomm_ab : a * b = b * a := s7_comm_orb2A H (IsConj.refl a) hb
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hbb : b * b = 1 := by simpa [pow_two] using hb2
  have hcc : c * c = 1 := by simpa [pow_two] using hc2
  have hccinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hac : a * c * a * c = b := by
    have h := hcsq
    rw [pow_two] at h
    rwa [show (a * c) * (a * c) = a * c * a * c by group] at h
  have hcac : c * a * c = a * b := by
    have h1 : a * (a * c * a * c) = a * b := by rw [hac]
    rw [show a * (a * c * a * c) = (a * a) * (c * a * c) by group, haa, one_mul] at h1
    exact h1
  have hb_eq : b = c * a * c * a := by
    have h1 : c * a * c * a = (a * b) * a := by rw [hcac]
    rw [h1, mul_assoc, ← hcomm_ab, ← mul_assoc, haa, one_mul]
  have hcbc : c * b * c = b := by
    conv_lhs => rw [hb_eq]
    rw [show c * (c * a * c * a) * c = a * c * a * c by
          rw [show c * (c * a * c * a) * c = (c * c) * (a * c * a * c) by group,
            hcc, one_mul]]
    exact hac
  have hbc : b * c = c * b := by
    have h := congrArg (fun x => c * x) hcbc
    rwa [show c * (c * b * c) = b * c by
          rw [show c * (c * b * c) = (c * c) * (b * c) by group, hcc, one_mul]] at h
  have hcabc : c * (a * b) * c = a := by
    calc c * (a * b) * c = c * a * (b * c) := by group
      _ = c * a * (c * b) := by rw [hbc]
      _ = (c * a * c) * b := by group
      _ = (a * b) * b := by rw [hcac]
      _ = a := by rw [mul_assoc, hbb, mul_one]
  have hφ2 : ∀ x : G, (MulAut.conj c) ((MulAut.conj c) x) = x := by
    intro x
    have h1 : (MulAut.conj c * MulAut.conj c) = (1 : MulAut G) := by
      rw [← map_mul, hcc, map_one]
    calc (MulAut.conj c) ((MulAut.conj c) x)
        = (MulAut.conj c * MulAut.conj c) x := by rw [MulAut.mul_apply]
      _ = (1 : MulAut G) x := by rw [h1]
      _ = x := rfl
  have hφa : (MulAut.conj c) a = a * b := by
    rw [MulAut.conj_apply, hccinv]; exact hcac
  have hφb : (MulAut.conj c) b = b := by
    rw [MulAut.conj_apply, hccinv]; exact hcbc
  have hφab : (MulAut.conj c) (a * b) = a := by
    rw [map_mul, hφa, hφb, mul_assoc, hbb, mul_one]
  have hQmap_le : ∀ g ∈ Gxy a b, c * g * c⁻¹ ∈ Gxy a b := by
    intro g hg
    have hga : a * g = g * a := mem_Gx.mp (mem_Gxy.mp hg).1
    have hgb : b * g = g * b := mem_Gx.mp (mem_Gxy.mp hg).2
    have hgab : (a * b) * g = g * (a * b) := by
      rw [mul_assoc, hgb, ← mul_assoc, hga, mul_assoc]
    rw [mem_Gxy]
    constructor
    · rw [mem_Gx]
      have hx : (MulAut.conj c) ((MulAut.conj c) a) = a := by rw [hφa, hφab]
      have hcomm : (MulAut.conj c) a * g = g * (MulAut.conj c) a := by
        rw [hφa]; exact hgab
      have h := starCent_conj_comm (MulAut.conj c) hx hcomm
      rwa [show (MulAut.conj c) g = c * g * c⁻¹ by
            rw [MulAut.conj_apply, hccinv]] at h
    · rw [mem_Gx]
      have hx : (MulAut.conj c) ((MulAut.conj c) b) = b := by rw [hφb, hφb]
      have hcomm : (MulAut.conj c) b * g = g * (MulAut.conj c) b := by
        rw [hφb]; exact hgb
      have h := starCent_conj_comm (MulAut.conj c) hx hcomm
      rwa [show (MulAut.conj c) g = c * g * c⁻¹ by
            rw [MulAut.conj_apply, hccinv]] at h
  let V : Subgroup G := Subgroup.closure ({a, b} : Set G)
  have haV : a ∈ V := Subgroup.subset_closure (by simp)
  have hbV : b ∈ V := Subgroup.subset_closure (by simp)
  have hV_le_Q : V ≤ Gxy a b := by
    change Subgroup.closure ({a, b} : Set G) ≤ Gxy a b
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_Gxy.mpr ⟨mem_Gx.mpr rfl, mem_Gx.mpr hcomm_ab.symm⟩
    · exact mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_ab, mem_Gx.mpr rfl⟩
  have hV_central_Q : ∀ v ∈ V, ∀ g ∈ Gxy a b, v * g = g * v := by
    intro v hv g hg
    have hVcent : V ≤ Subgroup.centralizer ({g} : Set G) := by
      change Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({g} : Set G)
      rw [Subgroup.closure_le]
      intro x hx
      change x ∈ Subgroup.centralizer ({g} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_Gx.mp (mem_Gxy.mp hg).1
      · exact mem_Gx.mp (mem_Gxy.mp hg).2
    exact Subgroup.mem_centralizer_singleton_iff.mp (hVcent hv)
  have hV_norm_c : ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    have hmap : V.map (MulAut.conj c).toMonoidHom ≤ V := by
      rw [Subgroup.map_le_iff_le_comap]
      change Subgroup.closure ({a, b} : Set G) ≤
        (Subgroup.closure ({a, b} : Set G)).comap (MulAut.conj c).toMonoidHom
      rw [Subgroup.closure_le]
      intro x hx
      change (MulAut.conj c) x ∈ V
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [hφa]; exact Subgroup.mul_mem _ haV hbV
      · rw [hφb]; exact hbV
    intro v hv
    have h := hmap (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)
    change (MulAut.conj c) v ∈ V at h
    rwa [show (MulAut.conj c) v = c * v * c⁻¹ by
          rw [MulAut.conj_apply, hccinv]] at h
  have hV_inf_A : V ⊓ derivedOf (Gxy a b) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8
      (H.fusion3.self.shape_2A b hb)
    have hcenter : ∀ s : alternatingGroup (Fin 8),
        s * e.symm ⟨v, hvA⟩ = e.symm ⟨v, hvA⟩ * s := by
      intro s
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (hV_central_Q v hvV (e s : G) (derivedOf_le (Gxy a b) (e s).2)).symm
    have ht1 : e.symm ⟨v, hvA⟩ = 1 := by
      have hmem : e.symm ⟨v, hvA⟩ ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
        rw [Subgroup.mem_center_iff]
        intro s
        exact hcenter s
      rw [alternatingGroup.center_eq_bot (α := Fin 8) (by rw [Nat.card_fin]; norm_num)] at hmem
      simpa using hmem
    have h1 : (⟨v, hvA⟩ : ↥(derivedOf (Gxy a b))) = 1 := by
      rw [← MulEquiv.apply_symm_apply e ⟨v, hvA⟩, ht1, map_one]
    exact congrArg Subtype.val h1
  let Q : Subgroup G := Gxy a b
  let ψ : ↥Q →* ↥Q :=
    { toFun := fun q => ⟨(MulAut.conj c) (q : G), hQmap_le (q : G) q.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp [map_mul] }
  have hψcomm : (_root_.commutator ↥Q).map ψ ≤ _root_.commutator ↥Q := by
    rw [Subgroup.map_le_iff_le_comap]
    change ⁅(⊤ : Subgroup ↥Q), ⊤⁆ ≤ (_root_.commutator ↥Q).comap ψ
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator trivial trivial
  have hc_norm_A : ∀ s ∈ derivedOf (Gxy a b), c * s * c⁻¹ ∈ derivedOf (Gxy a b) := by
    intro s hs
    change s ∈ (_root_.commutator ↥Q).map Q.subtype at hs
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hs
    have hψq : ψ q ∈ _root_.commutator ↥Q :=
      hψcomm (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    have hmem : (ψ q : G) ∈ derivedOf (Gxy a b) := by
      change (ψ q : G) ∈ (_root_.commutator ↥Q).map Q.subtype
      exact Subgroup.mem_map.mpr ⟨ψ q, hψq, rfl⟩
    have hψcoeeq : (ψ q : G) = c * (q : G) * c⁻¹ := by
      change (MulAut.conj c) (q : G) = c * (q : G) * c⁻¹
      rw [MulAut.conj_apply, hccinv]
    rw [← hqeq]
    change c * (q : G) * c⁻¹ ∈ derivedOf (Gxy a b)
    rw [← hψcoeeq]
    exact hmem
  have hne_ab : a ≠ b := by
    intro hab_eq
    have h1 : a * b = 1 := by rw [← hab_eq]; exact haa
    exact ha1 (isConj_one_left.mp (by simpa [h1] using hb.2))
  have hdec : ∀ g ∈ Gxy a b, ∃ u ∈ V, ∃ s ∈ derivedOf (Gxy a b), g = u * s :=
    exists_mul_eq_of_isShapeTwoTwoTimesA8 (H.fusion3.self.shape_2A b hb) ha2 hb2 hcomm_ab
      ha1 hb1 hne_ab
  have hbQ : b ∈ Gxy a b := mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_ab, mem_Gx.mpr rfl⟩
  have hbC : b ∈ Gxy a b ⊓ Gx c := Subgroup.mem_inf.mpr ⟨hbQ, mem_Gx.mpr hbc.symm⟩
  have hbA : b ∉ derivedOf (Gxy a b) := by
    intro hbA'
    have hmem : b ∈ V ⊓ derivedOf (Gxy a b) := Subgroup.mem_inf.mpr ⟨hbV, hbA'⟩
    rw [hV_inf_A] at hmem
    exact hb1 (Subgroup.mem_bot.mp hmem)
  have hmain : ∀ g ∈ Gxy a b ⊓ Gx c,
      g * b ∈ derivedOf (Gxy a b) ∨ g ∈ derivedOf (Gxy a b) := by
    intro g hg
    obtain ⟨hgQ, hgc⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨u, huV, s, hsA, hgs⟩ := hdec g hgQ
    by_cases hgA : g ∈ derivedOf (Gxy a b)
    · exact Or.inr hgA
    · left
      have hgc' : c * g = g * c := mem_Gx.mp hgc
      have hcgc : c * g * c = g := by rw [hgc', mul_assoc, hcc, mul_one]
      have hsQ : s ∈ Gxy a b := derivedOf_le (Gxy a b) hsA
      have hu_ne : u ≠ 1 := by
        intro hu1
        exact hgA (by rw [hgs, hu1, one_mul]; exact hsA)
      have hcscA : c * s * c ∈ derivedOf (Gxy a b) := by
        have h := hc_norm_A s hsA
        rwa [hccinv] at h
      have hcucV : c * u * c ∈ V := by
        have h := hV_norm_c u huV
        rwa [hccinv] at h
      have hfix : c * u * c = u := by
        have h1 : c * g * c = (c * u * c) * (c * s * c) := by
          rw [hgs, show (c * u * c) * (c * s * c) = c * (u * s) * c by
                rw [show (c * u * c) * (c * s * c) = c * u * (c * c) * s * c by group,
                  hcc, mul_one]
                group]
        have h2 : (c * u * c) * (c * s * c) = u * s := by rw [← h1, hcgc, hgs]
        have h3 : u⁻¹ * (c * u * c) = s * (c * s * c)⁻¹ := by
          have h := congrArg (fun x => u⁻¹ * x * (c * s * c)⁻¹) h2
          rw [show u⁻¹ * ((c * u * c) * (c * s * c)) * (c * s * c)⁻¹ = u⁻¹ * (c * u * c) by
                group,
              show u⁻¹ * (u * s) * (c * s * c)⁻¹ = s * (c * s * c)⁻¹ by group] at h
          exact h
        have h4 : u⁻¹ * (c * u * c) ∈ V := V.mul_mem (V.inv_mem huV) hcucV
        have h5 : u⁻¹ * (c * u * c) ∈ derivedOf (Gxy a b) := by
          rw [h3]
          exact (derivedOf (Gxy a b)).mul_mem hsA ((derivedOf (Gxy a b)).inv_mem hcscA)
        have h6 : u⁻¹ * (c * u * c) = 1 := by
          have hmem : u⁻¹ * (c * u * c) ∈ V ⊓ derivedOf (Gxy a b) :=
            Subgroup.mem_inf.mpr ⟨h4, h5⟩
          rw [hV_inf_A] at hmem
          exact Subgroup.mem_bot.mp hmem
        calc c * u * c = u * (u⁻¹ * (c * u * c)) := by group
          _ = u * 1 := by rw [h6]
          _ = u := mul_one u
      have hu_cases : u = 1 ∨ u = a ∨ u = b ∨ u = a * b :=
        eq_of_mem_closure_two ha2 hb2 hcomm_ab huV
      have hu_eq_b : u = b := by
        rcases hu_cases with hu1 | hua | hub | huab
        · exact absurd hu1 hu_ne
        · exfalso
          rw [hua] at hfix
          rw [hcac] at hfix
          have h2 : a * (a * b) = a * a := congrArg (fun x => a * x) hfix
          rw [show a * (a * b) = b by rw [← mul_assoc, haa, one_mul], haa] at h2
          exact hb1 h2
        · exact hub
        · exfalso
          rw [huab] at hfix
          rw [hcabc] at hfix
          have h2 : a * a = a * (a * b) := congrArg (fun x => a * x) hfix
          rw [show a * (a * b) = b by rw [← mul_assoc, haa, one_mul], haa] at h2
          exact hb1 h2.symm
      have hbs : b * s = s * b := hV_central_Q b hbV s hsQ
      have hbse : (b * s) * b = s := by
        calc (b * s) * b = b * (s * b) := mul_assoc b s b
          _ = b * (b * s) := by rw [hbs]
          _ = (b * b) * s := (mul_assoc b b s).symm
          _ = s := by rw [hbb, one_mul]
      rw [hgs, hu_eq_b, hbse]
      exact hsA
  have hidx : (derivedOf (Gxy a b)).relIndex (Gxy a b ⊓ Gx c) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    exact ⟨b, hbC, hbA, fun g hg => hmain g hg⟩
  have hcardC : Nat.card ↥(Gxy a b ⊓ Gx c) = 1440 := by
    simpa using H.tableIV.self.card_stab b hb 2 c hc
  have hrel := Subgroup.relIndex_mul_card (H := derivedOf (Gxy a b)) (K := Gxy a b ⊓ Gx c)
  rw [hidx, hcardC] at hrel
  rw [← inf_assoc, inf_eq_left.mpr (derivedOf_le (Gxy a b))] at hrel
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
