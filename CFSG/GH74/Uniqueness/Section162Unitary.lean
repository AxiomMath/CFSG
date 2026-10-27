module

public import CFSG.GH74.Uniqueness.Section162Basic
public import CFSG.GH74.Uniqueness.Bender.Commuting

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem BenderSub.mk_mem_rootCenter
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) {T : Sylow 2 (↥F ⧸ center ↥F)}
    (hT : ((M ⊓ F).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)))
    {w : X} (hwZ : w ∈ Z) (hwM : w ∈ M) (hwF : w ∈ F) :
    QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ∈ Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) ∧
      QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ≠ 1 := by
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  have hodd := A2.odd_card_center_of_benderSub hB
  have hw2 : orderOf (⟨w, hwF⟩ : ↥F) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact S.invariant.1 w hwZ
  have hne : QuotientGroup.mk' (center ↥F) ⟨w, hwF⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨w, hwF⟩ : ↥F) ∈ center ↥F := (QuotientGroup.eq_one_iff _).mp h1
    exact CFSG.OddInversion.notMem_of_odd_card hodd hw2 hmem
  apply hc.involution_iff.mp
  refine ⟨(A2.mk_mem_normalizer_iff S hB hT _).mpr hwM, orderOf_eq_prime ?_ hne⟩
  have hww : (⟨w, hwF⟩ : ↥F) * ⟨w, hwF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one hwZ)
  rw [sq, ← map_mul, hww, map_one]

theorem BenderSub.exists_mem_of_mem_rootCenter
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) {T : Sylow 2 (↥F ⧸ center ↥F)}
    (hT : ((M ⊓ F).subgroupOf F).map (QuotientGroup.mk' (center ↥F)) =
      normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)))
    {x : ↥F ⧸ center ↥F} (hx : x ∈ Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)))
    (hx1 : x ≠ 1) :
    ∃ w : ↥F, (w : X) ∈ Z ∧ (w : X) ∈ M ∧ QuotientGroup.mk' (center ↥F) w = x := by
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) x
  have hgM : (g : X) ∈ M :=
    (A2.mk_mem_normalizer_iff S hB hT g).mp (Bender.le_borel _ (Bender.rootCenter_le _ hx))
  set k := Nat.card (center ↥F) with hk
  have hodd : Odd k := A2.odd_card_center_of_benderSub hB
  have hxx : QuotientGroup.mk' (center ↥F) g * QuotientGroup.mk' (center ↥F) g = 1 :=
    hc.center_sq _ hx
  have hpow : QuotientGroup.mk' (center ↥F) (g ^ k) = QuotientGroup.mk' (center ↥F) g := by
    obtain ⟨m, hm⟩ := hodd
    rw [map_pow, hm, pow_succ, pow_mul, sq, hxx, one_pow, one_mul]
  have hg2 : g * g ∈ center ↥F := by
    rw [← QuotientGroup.eq_one_iff]
    exact hxx
  have hsq : g ^ k * g ^ k = 1 := by
    have h1 : (⟨g * g, hg2⟩ : center ↥F) ^ k = 1 := pow_card_eq_one'
    have h2 : (g * g) ^ k = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [← pow_add, ← two_mul, pow_mul, sq]
    exact h2
  have hne : g ^ k ≠ 1 := by
    intro h1
    apply hx1
    rw [← hpow, h1, map_one]
  have hord : orderOf (g ^ k) = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) hne
  refine ⟨g ^ k, hB.invol _ (g ^ k).2 (by rw [Subgroup.orderOf_coe]; exact hord), ?_, hpow⟩
  rw [Subgroup.coe_pow]
  exact M.pow_mem hgM k

theorem ZDSetup.lemma162_unitary
    (S : ZDSetup X Z M) {F : Subgroup X} {n e : ℕ}
    (hB : BenderSub Z M F n 3 e) {t z : X} (htZ : t ∈ Z) (htM : t ∉ M) (htF : t ∈ F)
    (hzZ : z ∈ Z) (hzM : z ∈ M) (hzF : z ∈ F) :
    Bender.BenderType ↥(fZero Z M F t) n 1 1 ∧
      ⁅zpowers t, (M ⊓ conjugate M t) ⊓ F⁆ ≤ fZero Z M F t ∧
      ∀ v : MulAut ↥F, v * v = 1 → (∀ x : ↥F, (x : X) = z ∨ (x : X) = t → v x = x) →
        ∀ x : ↥F, (x : X) ∈ fZero Z M F t → v x = x := by
  set π := QuotientGroup.mk' (center ↥F) with hπ
  have hodd := A2.odd_card_center_of_benderSub hB
  obtain ⟨T, hT⟩ := hB.borel
  have hK := hB.bender
  have hn2 : 2 ≤ n := hK.two_le.2
  set t' : ↥F := ⟨t, htF⟩ with ht'def
  set z' : ↥F := ⟨z, hzF⟩ with hz'def
  have ht't' : t' * t' = 1 := Subtype.ext (S.invariant.mul_self_eq_one htZ)
  have htinv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht't'
  have htb : π t' * π t' = 1 := by rw [← map_mul, ht't', map_one]
  have htbT : π t' ∉ Bender.borel (T : Subgroup (↥F ⧸ center ↥F)) := fun h =>
    htM ((A2.mk_mem_normalizer_iff S hB hT t').mp h)
  have hc := hK.benderCore T htb htbT
  obtain ⟨hzR, hz1⟩ := hB.mk_mem_rootCenter S hT hzZ hzM hzF
  obtain ⟨hL3, ⟨φ⟩⟩ := hK.lemma_3_2_h_unitary T htb htbT hzR hz1
  set Lb := Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) ⊔ zpowers (π t') with hLb
  set F₀ := fZero Z M F t with hF₀
  have hF₀F : F₀ ≤ F := fZero_le htF
  set ψ : ↥F₀ →* ↥F ⧸ center ↥F := π.comp (Subgroup.inclusion hF₀F) with hψ
  have hrange : ψ.range = Lb := by
    apply le_antisymm
    · have hle : F₀ ≤ (Lb.comap π).map F.subtype := by
        refine fZero_le_of (fun w hwZ hwM hwF => ⟨⟨w, hwF⟩, ?_, rfl⟩) ⟨t', ?_, rfl⟩
        · exact mem_sup_left (hB.mk_mem_rootCenter S hT hwZ hwM hwF).1
        · exact mem_sup_right (mem_zpowers _)
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle x.2
      have hyx' : y = Subgroup.inclusion hF₀F x := Subtype.ext hyx
      rw [hyx'] at hy
      exact hy
    · refine sup_le (fun x hx => ?_) (zpowers_le.mpr ⟨⟨t, t_mem_fZero⟩, rfl⟩)
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      obtain ⟨w, hwZ, hwM, hwx⟩ := hB.exists_mem_of_mem_rootCenter S hT hx hx1
      exact ⟨⟨w, mem_fZero_of_mem hwZ hwM w.2⟩, hwx⟩
  have hLbB : Bender.BenderType ↥Lb n 1 1 := Bender.BenderType.linear n hn2 φ
  have hLbc : center ↥Lb = ⊥ := hLbB.center_eq_bot
  have hcenter : center ↥F₀ = ψ.ker := by
    apply le_antisymm
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hxr : ψ x ∈ Lb := by rw [← hrange]; exact ⟨x, rfl⟩
      have hcen : (⟨ψ x, hxr⟩ : ↥Lb) ∈ center ↥Lb := by
        rw [mem_center_iff]
        intro y
        obtain ⟨y', hy'⟩ : (y : ↥F ⧸ center ↥F) ∈ ψ.range := by rw [hrange]; exact y.2
        apply Subtype.ext
        change (y : ↥F ⧸ center ↥F) * ψ x = ψ x * y
        rw [← hy', ← map_mul, ← map_mul, mem_center_iff.mp hx y']
      rw [hLbc, mem_bot] at hcen
      exact congrArg Subtype.val hcen
    · intro x hx
      have hx' : Subgroup.inclusion hF₀F x ∈ center ↥F :=
        (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := congrArg Subtype.val (mem_center_iff.mp hx' (Subgroup.inclusion hF₀F y))
      exact h1
  have hquot : (↥F₀ ⧸ center ↥F₀) ≃* CFSG.Theory.Comparator.PSL2Model n :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      ((QuotientGroup.quotientKerEquivRange ψ).trans ((MulEquiv.subgroupCongr hrange).trans φ))
  have hBq : Bender.BenderType (↥F₀ ⧸ center ↥F₀) n 1 1 := Bender.BenderType.linear n hn2 hquot
  have hodd0 : Odd (Nat.card (center ↥F₀)) := by
    rw [hcenter]
    have hle : ψ.ker.map (Subgroup.inclusion hF₀F) ≤ center ↥F := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hF₀F)] at h1
    exact Odd.of_dvd_nat hodd h1
  have hcen0 : center ↥F₀ = ⊥ := center_eq_bot_of_benderType (Or.inl rfl)
    (closure_mul_self_fZero S.invariant (S.invariant.mul_self_eq_one htZ)) hodd0 hBq
  have hker : ψ.ker = ⊥ := hcenter.symm.trans hcen0
  refine ⟨benderType_of_center_eq_bot hBq hcen0, ?_, ?_⟩
  ·
    have hcomm_t : ∀ d ∈ M, d ∈ conjugate M t → ∀ hdF : d ∈ F, ⁅t, d⁆ ∈ F₀ := by
      intro d hdM hdMt hdF
      set d' : ↥F := ⟨d, hdF⟩ with hd'def
      set w' : ↥F := ⁅t', d'⁆ with hw'
      have hdcart : π d' ∈ Bender.cartan (T : Subgroup (↥F ⧸ center ↥F)) (π t') := by
        refine mem_inf.mpr ⟨(A2.mk_mem_normalizer_iff S hB hT d').mpr hdM, ?_⟩
        rw [Bender.mem_conjugate_iff_mul_inv]
        have h1 : t * d * t⁻¹ ∈ M := mem_conjugate_iff.mp hdMt
        have h2 : π (t' * d' * t'⁻¹) ∈ Bender.borel (T : Subgroup (↥F ⧸ center ↥F)) :=
          (A2.mk_mem_normalizer_iff S hB hT (t' * d' * t'⁻¹)).mpr h1
        rwa [map_mul, map_mul, map_inv] at h2
      have hwLb : π w' ∈ Lb := by
        rw [← hL3]
        apply mem_sup_right
        have h1 : π w' = ⁅π t', π d'⁆ := map_commutatorElement π t' d'
        rw [h1, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (mem_zpowers _) hdcart
      obtain ⟨f, hf⟩ : π w' ∈ ψ.range := by rw [hrange]; exact hwLb
      set f' : ↥F := Subgroup.inclusion hF₀F f with hf'def
      set c : ↥F := f'⁻¹ * w' with hcdef
      have hcZ : c ∈ center ↥F := QuotientGroup.eq.mp hf
      have hcc : ∀ y : ↥F, c * y = y * c := fun y => (mem_center_iff.mp hcZ y).symm
      have hcinv : ∀ y : ↥F, c⁻¹ * y = y * c⁻¹ := fun y => by
        calc c⁻¹ * y = c⁻¹ * (y * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * y) * c⁻¹ := by rw [hcc y]
          _ = y * c⁻¹ := by group
      have hw'eq : w' = f' * c := by rw [hcdef]; group
      have hinv : t' * w' * t'⁻¹ = w'⁻¹ := by
        rw [hw', commutatorElement_def]
        calc t' * (t' * d' * t'⁻¹ * d'⁻¹) * t'⁻¹ = (t' * t') * d' * t'⁻¹ * d'⁻¹ * t'⁻¹ := by
              group
          _ = d' * t'⁻¹ * d'⁻¹ * t'⁻¹ := by rw [ht't']; group
          _ = d' * t' * d'⁻¹ * t'⁻¹ := by rw [htinv]
          _ = (t' * d' * t'⁻¹ * d'⁻¹)⁻¹ := by group
      have key : f' * t' * f' * t'⁻¹ = (c * c)⁻¹ := by
        have h1 : t' * (f' * c) * t'⁻¹ = (f' * c)⁻¹ := by rw [← hw'eq]; exact hinv
        have h2 : t' * (f' * c) * t'⁻¹ = t' * f' * t'⁻¹ * c := by
          calc t' * (f' * c) * t'⁻¹ = t' * f' * (c * t'⁻¹) := by group
            _ = t' * f' * (t'⁻¹ * c) := by rw [hcc t'⁻¹]
            _ = t' * f' * t'⁻¹ * c := by group
        have h4 : t' * f' * t'⁻¹ * c = c⁻¹ * f'⁻¹ := by rw [← h2, h1, mul_inv_rev]
        calc f' * t' * f' * t'⁻¹ = f' * (t' * f' * t'⁻¹ * c) * c⁻¹ := by group
          _ = f' * (c⁻¹ * f'⁻¹) * c⁻¹ := by rw [h4]
          _ = (f' * c⁻¹) * f'⁻¹ * c⁻¹ := by group
          _ = (c⁻¹ * f') * f'⁻¹ * c⁻¹ := by rw [hcinv f']
          _ = (c * c)⁻¹ := by group
      set t₀ : ↥F₀ := ⟨t, t_mem_fZero⟩ with ht₀
      have hincl : Subgroup.inclusion hF₀F (f * t₀ * f * t₀⁻¹) = (c * c)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv]
        exact key
      have hg₀ : f * t₀ * f * t₀⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        change π (Subgroup.inclusion hF₀F (f * t₀ * f * t₀⁻¹)) = 1
        rw [hincl, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact (center ↥F).inv_mem ((center ↥F).mul_mem hcZ hcZ)
      rw [hker, mem_bot] at hg₀
      have hcc1 : c * c = 1 := by
        have h1 := congrArg (Subgroup.inclusion hF₀F) hg₀
        rw [hincl, map_one] at h1
        exact inv_eq_one.mp h1
      have hc1 : c = 1 := eq_one_of_mem_of_sq_eq_one hodd hcZ hcc1
      have hwf : w' = f' := by rw [hw'eq, hc1, mul_one]
      have hmem : (w' : X) ∈ F₀ := by
        rw [hwf]
        exact f.2
      simpa [hw', commutatorElement_def] using hmem
    rw [Subgroup.commutator_le]
    intro g hg d hd
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    obtain ⟨hdD, hdF⟩ := mem_inf.mp hd
    obtain ⟨hdM, hdMt⟩ := mem_inf.mp hdD
    have ht2 : t ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact S.invariant.mul_self_eq_one htZ
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, ht2, one_zpow, commutatorElement_one_left]
      exact one_mem _
    · rw [zpow_add_one, zpow_mul, ht2, one_zpow, one_mul]
      exact hcomm_t d hdM hdMt hdF
  ·
    intro v hv hvzt x hx
    have hvz : v z' = z' := hvzt z' (Or.inl rfl)
    have hvt : v t' = t' := hvzt t' (Or.inr rfl)
    have hchar : (center ↥F).map (v : ↥F →* ↥F) = center ↥F := by
      have := Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (center ↥F).Characteristic) v
      rwa [MulEquiv.toMonoidHom_eq_coe] at this
    set vb : MulAut (↥F ⧸ center ↥F) := QuotientGroup.congr (center ↥F) (center ↥F) v hchar
      with hvb
    have hvb_mk : ∀ y : ↥F, vb (π y) = π (v y) := fun y =>
      QuotientGroup.congr_mk (center ↥F) (center ↥F) v hchar y
    have hvb2 : vb * vb = 1 := by
      ext y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center ↥F) y
      rw [MulAut.mul_apply, MulAut.one_apply, hvb_mk, hvb_mk]
      have h1 : v (v y) = y := by rw [← MulAut.mul_apply, hv, MulAut.one_apply]
      rw [h1]
    have hvbz : vb (π z') = π z' := by rw [hvb_mk, hvz]
    have hKc : center (↥F ⧸ center ↥F) = ⊥ := hK.center_eq_bot
    have hzz : π z' * π z' = 1 := hc.center_sq _ hzR
    have hfix : ∀ w ∈ Z, w ∈ M → ∀ hwF : w ∈ F, v ⟨w, hwF⟩ = ⟨w, hwF⟩ := by
      intro w hwZ hwM hwF
      obtain ⟨hwR, -⟩ := hB.mk_mem_rootCenter S hT hwZ hwM hwF
      have hww : π ⟨w, hwF⟩ * π ⟨w, hwF⟩ = 1 := hc.center_sq _ hwR
      have hwz : π ⟨w, hwF⟩ * π z' = π z' * π ⟨w, hwF⟩ :=
        (Bender.mem_rootCenter_iff.mp hzR).2 _ (Bender.rootCenter_le _ hwR)
      have hvbw : vb (π ⟨w, hwF⟩) = π ⟨w, hwF⟩ := by
        by_cases hinner : ∃ g : ↥F ⧸ center ↥F, ∀ y, vb y = g * y * g⁻¹
        · obtain ⟨g, hg⟩ := hinner
          have hgg : g * g = 1 := by
            have hgc : g * g ∈ center (↥F ⧸ center ↥F) := by
              rw [mem_center_iff]
              intro y
              have h1 : vb (vb y) = y := by rw [← MulAut.mul_apply, hvb2, MulAut.one_apply]
              rw [hg, hg] at h1
              calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
                _ = g * g * y := by group
            rw [hKc, mem_bot] at hgc
            exact hgc
          have hgz : g * π z' = π z' * g := by
            have h1 := hvbz
            rw [hg] at h1
            calc g * π z' = (g * π z' * g⁻¹) * g := by group
              _ = π z' * g := by rw [h1]
          rw [hg, hK.commute_of_commute_involutions hgg hzz hww hz1 hgz hwz]
          group
        · exact hK.fixed_of_commute_unitary vb hvb2 hinner hzz hz1 hvbz hww hwz
      have hw1 : (⟨w, hwF⟩ : ↥F) * ⟨w, hwF⟩ = 1 := Subtype.ext (S.invariant.mul_self_eq_one hwZ)
      have hvw2 : v ⟨w, hwF⟩ * v ⟨w, hwF⟩ = 1 := by rw [← map_mul, hw1, map_one]
      have hmem : (v ⟨w, hwF⟩)⁻¹ * ⟨w, hwF⟩ ∈ center ↥F :=
        QuotientGroup.eq.mp ((hvb_mk _).symm.trans hvbw)
      exact A2.eq_of_inv_mul_mem_of_odd hodd le_rfl hvw2 hw1 hmem
    have hle : F₀ ≤ (MonoidHom.eqLocus (v : ↥F →* ↥F) (MonoidHom.id ↥F)).map F.subtype :=
      fZero_le_of (fun w hwZ hwM hwF => ⟨⟨w, hwF⟩, hfix w hwZ hwM hwF, rfl⟩) ⟨t', hvt, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

end CFSG.GH74.Uniqueness
