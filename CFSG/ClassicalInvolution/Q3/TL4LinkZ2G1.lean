module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2B
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4Sp6
public import Certificates.Certificate416001
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

namespace Sp62S

theorem map_tab (l : List (Equiv.Perm (Fin 36))) : l.map tab = l := by
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x _ => tab_eq x

theorem mem_sqRoots {r x : Equiv.Perm (Fin 36)} {E : List (Equiv.Perm (Fin 36))} :
    x ∈ sqRoots r E ↔ x ∈ E ∧ x * x = r := by
  rw [sqRoots, map_tab, List.mem_filter, decide_eq_true_iff]

theorem sqCheck_spec {r : Equiv.Perm (Fin 36)} {E : List (Equiv.Perm (Fin 36))}
    (h : sqCheck r E = true) {s : Equiv.Perm (Fin 36)} (hs : s ∈ E) (hs2 : s * s = 1) :
    (∀ u ∈ E, u * u = r → u * s = s * u) ∨
      ∀ x ∈ E, ∀ y ∈ E, x * x = r → y * y = r → x * s = s * x → y * s = s * y →
        y * x * y⁻¹ ≠ x⁻¹ := by
  simp only [sqCheck, Bool.or_eq_true, List.all_eq_true] at h
  rcases h with h | h
  · refine Or.inl fun u hu hur => absurd (mem_sqRoots.2 ⟨hu, hur⟩) ?_
    rw [List.isEmpty_iff.mp h]
    exact List.not_mem_nil
  have h1 := h s hs
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, tab_eq] at h1
  rcases h1 with h1 | h1
  · exact absurd hs2 h1
  simp only [sqStep, Bool.or_eq_true, List.all_eq_true, List.mem_filter, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, and_imp] at h1
  rcases h1 with h1 | h1
  · exact Or.inl fun u hu hur => h1 u (mem_sqRoots.2 ⟨hu, hur⟩)
  · exact Or.inr fun x hx y hy hxr hyr hxs hys =>
      h1 x (mem_sqRoots.2 ⟨hx, hxr⟩) hxs y (mem_sqRoots.2 ⟨hy, hyr⟩) hys

theorem sq_parts :
    sqCheck sp6Rep1 (enumeration sp6CentQ1) = true ∧
      sqCheck sp6Rep2 (enumeration sp6CentQ2) = true ∧
      sqCheck sp6Rep3 (enumeration sp6CentQ3) = true ∧
      sqCheck sp6Rep4 (enumeration sp6CentQ4) = true := by
  have h := Certificates.certificate416001
  simp only [sPropCheck, Bool.and_eq_true, tab_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem valid_of_centCheck {Q : RawSchreierDatum 36} {c : ℕ}
    {gs reps : List (Equiv.Perm (Fin 36))} {r : Equiv.Perm (Fin 36)}
    (h : centCheck Q c gs reps r = true) : ValidSchreier Q := by
  simp only [centCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1

theorem commute_of_sqCheck {r : Equiv.Perm (Fin 36)} {Q : RawSchreierDatum 36}
    (hQv : ValidSchreier Q) (hCQ : centralizerIn co3X36 r = Q.originalSubgroup)
    (hc : sqCheck r (enumeration Q) = true) {s u x y : Equiv.Perm (Fin 36)} (hs : s ∈ co3X36)
    (hu : u ∈ co3X36) (hx : x ∈ co3X36) (hy : y ∈ co3X36) (hxx : x * x = r) (hyy : y * y = r)
    (hyx : y * x * y⁻¹ = x⁻¹) (huu : u * u = r) (hs2 : s * s = 1) (hxs : x * s = s * x)
    (hys : y * s = s * y) : u * s = s * u := by
  have hmem : ∀ g ∈ co3X36, g * r = r * g → g ∈ enumeration Q := fun g hg hgr => by
    rw [mem_enumeration_iff Q hQv, ← hCQ]
    exact mem_centralizerIn.2 ⟨hg, hgr⟩
  have hsq : ∀ g : Equiv.Perm (Fin 36), g * g = r → g * r = r * g := fun g hg => by
    rw [← hg]
    exact (mul_assoc g g g).symm
  have hsr : s * r = r * s := by
    rw [← hxx]
    exact (Commute.mul_left hxs hxs).eq.symm
  rcases sqCheck_spec hc (hmem s hs hsr) hs2 with h | h
  · exact h u (hmem u hu (hsq u huu)) huu
  · exact absurd hyx (h x (hmem x hx (hsq x hxx)) y (hmem y hy (hsq y hyy)) hxx hyy hxs hys)

theorem commute_model
    {s u x y : Equiv.Perm (Fin 36)}
    (hs : s ∈ co3X36) (hu : u ∈ co3X36) (hx : x ∈ co3X36) (hy : y ∈ co3X36) (hz : x * x ≠ 1)
    (hyy : y * y = x * x) (hyx : y * x * y⁻¹ = x⁻¹) (huu : u * u = x * x) (hs2 : s * s = 1)
    (hxs : x * s = s * x) (hys : y * s = s * y) : u * s = s * u := by
  have hz2 : x * x * (x * x) = 1 := by
    have h1 : y * (x * x) * y⁻¹ = x⁻¹ * x⁻¹ := by
      calc y * (x * x) * y⁻¹ = y * x * y⁻¹ * (y * x * y⁻¹) := by group
        _ = x⁻¹ * x⁻¹ := by rw [hyx]
    have h2 : y * (x * x) * y⁻¹ = x * x := by
      rw [← hyy]
      group
    rw [mul_eq_one_iff_eq_inv, mul_inv_rev, ← h1, h2]
  have hzo : orderOf (x * x) = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz
  obtain ⟨r, hr, c, hc, hzc⟩ :=
    co3X36_involution_centralizers.1 (x * x) (co3X36.mul_mem hx hx) hzo
  set κ : MulAut (Equiv.Perm (Fin 36)) := MulAut.conj c⁻¹ with hκ
  have hκX : ∀ g ∈ co3X36, κ g ∈ co3X36 := fun g hg => by
    rw [hκ, MulAut.conj_apply]
    exact co3X36.mul_mem (co3X36.mul_mem (co3X36.inv_mem hc) hg)
      (co3X36.inv_mem (co3X36.inv_mem hc))
  have hκr : κ x * κ x = r := by
    rw [← map_mul, hzc, hκ, MulAut.conj_apply]
    group
  have key : ∀ Q : RawSchreierDatum 36, ValidSchreier Q →
      centralizerIn co3X36 r = Q.originalSubgroup → sqCheck r (enumeration Q) = true →
        u * s = s * u := by
    intro Q hQv hCQ hck
    apply κ.injective
    rw [map_mul, map_mul]
    exact commute_of_sqCheck hQv hCQ hck (hκX s hs) (hκX u hu) (hκX x hx) (hκX y hy) hκr
      (by rw [← map_mul, hyy, map_mul, hκr]) (by rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv])
      (by rw [← map_mul, huu, map_mul, hκr]) (by rw [← map_mul, hs2, map_one])
      (by rw [← map_mul, hxs, map_mul]) (by rw [← map_mul, hys, map_mul])
  have hCQ : ∀ (r' : Equiv.Perm (Fin 36)) (Q : RawSchreierDatum 36),
      centralizerIn sp6Q.originalSubgroup r' = Q.originalSubgroup →
        centralizerIn co3X36 r' = Q.originalSubgroup := fun r' Q h => by
    rwa [← sp6Q_originalSubgroup]
  obtain ⟨h1, h2, h3, h4⟩ := sq_parts
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact key _ (valid_of_centCheck sp6_cent_check₁) (hCQ _ _ sp6_cent_spec₁.1) h1
  · exact key _ (valid_of_centCheck sp6_cent_check₂) (hCQ _ _ sp6_cent_spec₂.1) h2
  · exact key _ (valid_of_centCheck sp6_cent_check₃) (hCQ _ _ sp6_cent_spec₃.1) h3
  · exact key _ (valid_of_centCheck sp6_cent_check₄) (hCQ _ _ sp6_cent_spec₄.1) h4

theorem commute_sp62
    {Q : Type} [Group Q]
    (hQ : LieModel Q .PSp 3 2 1) {s u x y : Q} (hz : x * x ≠ 1) (hyy : y * y = x * x)
    (hyx : y * x * y⁻¹ = x⁻¹) (huu : u * u = x * x) (hs2 : s * s = 1) (hxs : x * s = s * x)
    (hys : y * s = s * y) : u * s = s * u := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hQ
  set φ : Q →* Equiv.Perm (Fin 36) := co3X36.subtype.comp e.toMonoidHom
  have hinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hmem : ∀ q, φ q ∈ co3X36 := fun q => (e q).2
  apply hinj
  rw [map_mul, map_mul]
  exact commute_model (hmem s) (hmem u) (hmem x) (hmem y)
    (by rw [← map_mul]; exact fun h => hz (hinj (h.trans (map_one φ).symm)))
    (by rw [← map_mul, ← map_mul, hyy]) (by rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv])
    (by rw [← map_mul, ← map_mul, huu]) (by rw [← map_mul, hs2, map_one])
    (by rw [← map_mul, ← map_mul, hxs]) (by rw [← map_mul, ← map_mul, hys])

theorem q8_rels :
    QuaternionGroup.a 1 * QuaternionGroup.a 1 = (QuaternionGroup.a 2 : QuaternionGroup 2) ∧
      QuaternionGroup.xa 0 * QuaternionGroup.xa 0 = (QuaternionGroup.a 2 : QuaternionGroup 2) ∧
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
        ((QuaternionGroup.a 1)⁻¹ : QuaternionGroup 2) ∧
      (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 ∧
      (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
  decide

theorem exists_quat_gens {G : Type*} [Group G] {P K : Subgroup G} {z : G} (hPK : P ≤ K)
    (hz : IsUniqueInvolution K z) (e : ↥P ≃* QuaternionGroup 2) :
    ∃ x ∈ P, ∃ y ∈ P, x * x = z ∧ y * y = z ∧ y * x * y⁻¹ = x⁻¹ := by
  let φ : QuaternionGroup 2 →* G := P.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hmem : ∀ q, φ q ∈ P := fun q => (e.symm q).2
  obtain ⟨h1, h2, h3, h4, h5⟩ := q8_rels
  have hz0 : φ (QuaternionGroup.a 2) = z := by
    rcases hz.unique _ (hPK (hmem _)) (by rw [← map_mul, h5, map_one]) with h | h
    · exact absurd (hφ (h.trans (map_one φ).symm)) h4
    · exact h
  refine ⟨φ (QuaternionGroup.a 1), hmem _, φ (QuaternionGroup.xa 0), hmem _, ?_, ?_, ?_⟩
  · rw [← map_mul, h1, hz0]
  · rw [← map_mul, h2, hz0]
  · rw [← map_inv, ← map_mul, ← map_mul, h3, map_inv]

end Sp62S

theorem gapTwinE4Sp62_of_certs :
    GapTwinE4Sp62 := by
  intro W _ _ Φ K K' k k' σ hT Q _ f hf hf2 hQ
  have : Finite Q := Finite.of_surjective f hf
  have h := hT.toTwinBase3
  have hQ' : PhilipHall.QuaternionBridge.ExLie Q := Or.inl hQ
  have hker : f.ker = Subgroup.center W :=
    le_antisymm (E3S3O.ker_le_center h f hf2) (E3S3O.center_le_ker h f hf hf2 hQ')
  have hσ : f.ker.map σ.toMonoidHom = f.ker := by
    rw [hker]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance σ
  have hτ := E3S3O.descend_apply f hf σ hσ
  obtain ⟨s, hs⟩ := Q3NM.mem_innSubgroup_iff.mp
    (ExitTwo.E4.aut_inner_of_lieModel_PSp hQ (E3S3O.descend f hf σ hσ))
  have hconj : ∀ w, s * f w * s⁻¹ = f (σ w) := fun w => by
    rw [← hτ, ← hs, MulAut.conj_apply]
  have hσσ : ∀ w, σ (σ w) = w := fun w => by
    have := congrArg (fun τ : MulAut W => τ w) hT.sq
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hfk : f k' = f k := by
    have h1 : k * k' ∈ f.ker := by
      rw [hker]
      exact h.center
    rw [MonoidHom.mem_ker, map_mul] at h1
    have h3 : f k * f k = 1 := by rw [← map_mul, h.invK.sq, map_one]
    calc f k' = f k * f k * f k' := by rw [h3, one_mul]
      _ = f k := by rw [mul_assoc, h1, mul_one]
  have hfk1 : f k ≠ 1 := fun h1 => E3S3O.not_mem_ker h f hf2 1 (by
    rw [MonoidHom.mem_ker]
    simpa using h1)
  obtain ⟨P, hP, hPfix⟩ := hT.fixK
  have eP : ↥P ≃* QuaternionGroup 2 := (h.fam.quat K h.memK P hP).some
  obtain ⟨x, hxP, y, hyP, hxx, hyy, hyx⟩ := Sp62S.exists_quat_gens hP.1 h.invK eP
  have hcomm : ∀ w ∈ P, f w * s = s * f w := fun w hw => by
    have h1 := hconj w
    rw [hPfix w hw] at h1
    calc f w * s = s * f w * s⁻¹ * s := by rw [h1]
      _ = s * f w := by group
  have hXX : f x * f x = f k := by rw [← map_mul, hxx]
  have hz : f x * f x ≠ 1 := by
    rw [hXX]
    exact hfk1
  have hYY : f y * f y = f x * f x := by rw [← map_mul, ← map_mul, hyy, hxx]
  have hYX : f y * f x * (f y)⁻¹ = (f x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hyx, map_inv]
  have hZ : Subgroup.center Q = ⊥ := by
    have : IsSimpleGroup Q := Vtx.isSimpleGroup_of_exLie hQ'
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hb | ht
    · exact hb
    · exfalso
      have hc : f x * f y = f y * f x :=
        Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top (f y)) (f x)
      apply hz
      rw [mul_eq_one_iff_eq_inv, ← hYX, ← hc]
      group
  have hs2 : s * s = 1 := by
    have h1 : s * s ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨w, rfl⟩ := hf q
      have e1 : s * (s * f w * s⁻¹) * s⁻¹ = f w := by rw [hconj, hconj, hσσ]
      calc f w * (s * s) = s * (s * f w * s⁻¹) * s⁻¹ * (s * s) := by rw [e1]
        _ = s * s * f w := by group
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨Q', hQ', hQ'σ, hQ'fix⟩ := hT.onK'
  have hK' : K' ∈ Φ := by
    obtain ⟨c, hc⟩ := h.memK'
    have hc' : conjSub c K = K' := hc
    rw [← hc']
    exact h.fam.hyp.conjInvariant c K h.memK
  have eQ' : ↥Q' ≃* QuaternionGroup 2 := (h.fam.quat K' hK' Q' hQ').some
  obtain ⟨b, hbQ, -, -, hbb, -, -⟩ := Sp62S.exists_quat_gens hQ'.1 h.invK' eQ'
  have hK'ker : K' ⊓ f.ker = ⊥ := E3S3O.inf_eq_bot_of_not_mem h.invK' hf2 (by
    rw [MonoidHom.mem_ker, hfk]
    exact hfk1)
  have hUU : f b * f b = f x * f x := by rw [← map_mul, hbb, hfk, hXX]
  have hUs := Sp62S.commute_sp62 hQ hz hYY hYX hUU hs2 (hcomm x hxP) (hcomm y hyP)
  have h1 : f (σ b) = f b := by
    rw [← hconj]
    calc s * f b * s⁻¹ = f b * s * s⁻¹ := by rw [← hUs]
      _ = f b := by group
  have h2 : b⁻¹ * σ b ∈ K' ⊓ f.ker :=
    ⟨K'.mul_mem (K'.inv_mem (hQ'.1 hbQ)) (hQ'.1 (hQ'σ b hbQ)), by
      show b⁻¹ * σ b ∈ f.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]⟩
  rw [hK'ker, Subgroup.mem_bot] at h2
  have h4 := hQ'fix b hbQ (inv_mul_eq_one.mp h2).symm
  rw [hbb] at h4
  exact h.invK'.ne_one h4

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
