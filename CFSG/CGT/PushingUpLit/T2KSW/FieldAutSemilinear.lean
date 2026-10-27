module

public import CFSG.CGT.PushingUpLit.T2KSW.Coord
public import CFSG.CGT.PushingUpLit.T2KSW.RD

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KR CFSG.CGT.PushingUpLit.BHS CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement

section Field

variable {F : Type} [Field F]

@[expose] noncomputable def fixCard (σ : F ≃+* F) : ℕ := Nat.card {c : F // σ c = c}

theorem fixCard_pos [Finite F] (σ : F ≃+* F) : 0 < fixCard σ := by
  have : Nonempty {c : F // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
  exact Nat.card_pos

theorem two_le_fixCard [Finite F] (σ : F ≃+* F) : 2 ≤ fixCard σ := by
  have : Nontrivial {c : F // σ c = c} :=
    ⟨⟨⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  exact Finite.one_lt_card

theorem card_twist_fixed_le [Finite F] (σ : F ≃+* F) (δ : F) :
    Nat.card {t : F // δ * σ t = t} ≤ fixCard σ := by
  classical
  by_cases h : ∃ t₀ : F, t₀ ≠ 0 ∧ δ * σ t₀ = t₀
  · obtain ⟨t₀, ht₀, hδ⟩ := h
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      exact ht₀ (by simpa using hδ.symm)
    have hσt₀ : σ t₀ ≠ 0 := by simpa using ht₀
    have key : ∀ t : F, δ * σ t = t → σ (t / t₀) = t / t₀ := by
      intro t ht
      rw [map_div₀]
      field_simp
      linear_combination (σ t₀) * ht - (σ t) * hδ
    refine Nat.card_le_card_of_injective
      (fun t : {t : F // δ * σ t = t} => (⟨t.1 / t₀, key t.1 t.2⟩ : {c : F // σ c = c})) ?_
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa [ht₀] using this
  · push Not at h
    have hsub : Subsingleton {t : F // δ * σ t = t} :=
      ⟨fun a b => Subtype.ext (by
        have h1 : a.1 = 0 := by
          by_contra h1
          exact h a.1 h1 a.2
        have h2 : b.1 = 0 := by
          by_contra h2
          exact h b.1 h2 b.2
        rw [h1, h2])⟩
    exact (Finite.card_le_one_iff_subsingleton.2 hsub).trans (two_le_fixCard σ |>.trans' (by omega))

theorem semilinear_apply {σ : F ≃+* F} {a : (Fin 2 → F) → (Fin 2 → F)}
    (hadd : ∀ w w', a (w + w') = a w + a w') (hsemi : ∀ (c : F) w, a (c • w) = σ c • a w)
    (w : Fin 2 → F) :
    a w = σ (w 0) • a (Pi.single 0 1) + σ (w 1) • a (Pi.single 1 1) := by
  have hw : w = w 0 • (Pi.single 0 1 : Fin 2 → F) + w 1 • (Pi.single 1 1 : Fin 2 → F) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hw]
  rw [hadd, hsemi, hsemi]

theorem card_fixed_le_sq [Finite F] (σ : F ≃+* F) (a : (Fin 2 → F) → (Fin 2 → F))
    (hadd : ∀ w w', a (w + w') = a w + a w') (hsemi : ∀ (c : F) w, a (c • w) = σ c • a w) :
    Nat.card {w : Fin 2 → F // a w = w} ≤ fixCard σ ^ 2 := by
  classical
  have h0 : a 0 = 0 := by simpa using hadd 0 0
  have hneg : ∀ w, a (-w) = - a w := fun w => by
    have := hadd w (-w)
    rw [add_neg_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  let Z : AddSubgroup (Fin 2 → F) :=
    { carrier := {w | a w = w}
      add_mem' := fun {x y} hx hy => by
        have hx' : a x = x := hx
        have hy' : a y = y := hy
        show a (x + y) = x + y
        rw [hadd, hx', hy']
      zero_mem' := h0
      neg_mem' := fun {x} hx => by
        have hx' : a x = x := hx
        show a (-x) = -x
        rw [hneg, hx'] }
  have hZcard : Nat.card {w : Fin 2 → F // a w = w} = Nat.card Z := rfl
  rw [hZcard]
  have hq1 : 1 ≤ fixCard σ := fixCard_pos σ
  by_cases hz : ∃ z : Fin 2 → F, z ≠ 0 ∧ a z = z
  · obtain ⟨z, hz0, haz⟩ := hz
    set p : Fin 2 → F := a (Pi.single 0 1) with hp
    set p' : Fin 2 → F := a (Pi.single 1 1) with hp'
    have hform : ∀ w, a w = σ (w 0) • p + σ (w 1) • p' := fun w => semilinear_apply hadd hsemi w
    set Δ : F := p 0 * p' 1 - p 1 * p' 0 with hΔ
    set d : (Fin 2 → F) → F := fun w => z 0 * w 1 - z 1 * w 0 with hd_def
    have hz' : z = σ (z 0) • p + σ (z 1) • p' := by
      have := hform z
      rwa [haz] at this
    have e0 : z 0 = σ (z 0) * p 0 + σ (z 1) * p' 0 := by
      have := congrFun hz' 0
      simpa using this
    have e1 : z 1 = σ (z 0) * p 1 + σ (z 1) * p' 1 := by
      have := congrFun hz' 1
      simpa using this
    have hd : ∀ w, d (a w) = Δ * σ (d w) := by
      intro w
      simp only [hd_def, hform w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hΔ]
      linear_combination (σ (w 0) * p 1 + σ (w 1) * p' 1) * e0 -
        (σ (w 0) * p 0 + σ (w 1) * p' 0) * e1
    let dHom : (Fin 2 → F) →+ F :=
      AddMonoidHom.mk' d (fun w w' => by simp only [hd_def, Pi.add_apply]; ring)
    let Λ : Z →+ F := dHom.comp Z.subtype
    have hΛ : ∀ w : Z, Λ w = d w.1 := fun w => rfl
    have hrange : Nat.card Λ.range ≤ fixCard σ := by
      refine (Nat.card_le_card_of_injective
        (fun t : Λ.range => (⟨t.1, ?_⟩ : {t : F // Δ * σ t = t})) ?_).trans
        (card_twist_fixed_le σ Δ)
      · obtain ⟨_, ⟨w, rfl⟩⟩ := t
        have hw : a w.1 = w.1 := w.2
        have := hd w.1
        rw [hw] at this
        exact this.symm
      · intro x y hxy
        exact Subtype.ext (congrArg (fun z : {t : F // Δ * σ t = t} => (z : F)) hxy)
    have hker : Nat.card Λ.ker ≤ fixCard σ := by
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz0
      have hi₀' : z i₀ ≠ 0 := hi₀
      have hprop : ∀ w : Fin 2 → F, d w = 0 → w = (w i₀ / z i₀) • z := by
        intro w hw
        simp only [hd_def] at hw
        ext j
        fin_cases i₀ <;> fin_cases j <;> simp at hi₀' ⊢ <;> field_simp <;>
          first | linear_combination hw | linear_combination -hw
      have hσ : ∀ w : Λ.ker, σ (w.1.1 i₀ / z i₀) = w.1.1 i₀ / z i₀ := by
        intro w
        have hw0 : d w.1.1 = 0 := w.2
        have hwa : a w.1.1 = w.1.1 := w.1.2
        have h1 := hprop _ hw0
        set c := w.1.1 i₀ / z i₀ with hc
        have h2 : σ c • z = c • z := by
          have : a (c • z) = c • z := by rw [← h1]; exact hwa
          rw [hsemi, haz] at this
          exact this
        have h3 := congrFun h2 i₀
        simp only [Pi.smul_apply, smul_eq_mul] at h3
        exact mul_right_cancel₀ hi₀' h3
      refine Nat.card_le_card_of_injective
        (fun w : Λ.ker => (⟨w.1.1 i₀ / z i₀, hσ w⟩ : {c : F // σ c = c})) ?_
      intro u v huv
      have huv' : u.1.1 i₀ / z i₀ = v.1.1 i₀ / z i₀ :=
        congrArg (fun c : {c : F // σ c = c} => (c : F)) huv
      have hu : d u.1.1 = 0 := u.2
      have hv : d v.1.1 = 0 := v.2
      apply Subtype.ext
      apply Subtype.ext
      calc u.1.1 = (u.1.1 i₀ / z i₀) • z := hprop u.1.1 hu
        _ = (v.1.1 i₀ / z i₀) • z := by rw [huv']
        _ = v.1.1 := (hprop v.1.1 hv).symm
    have := AddSubgroup.card_ker_mul_card_range Λ
    rw [← this, sq]
    exact Nat.mul_le_mul hker hrange
  · push Not at hz
    have hsub : Subsingleton Z :=
      ⟨fun x y => Subtype.ext (by
        have h1 : x.1 = 0 := by
          by_contra h
          exact hz x.1 h x.2
        have h2 : y.1 = 0 := by
          by_contra h
          exact hz y.1 h y.2
        rw [h1, h2])⟩
    calc Nat.card Z ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
      _ ≤ fixCard σ ^ 2 := Nat.one_le_pow _ _ hq1

theorem card_line_fixed_le [Finite F] (σ : F ≃+* F) (a : (Fin 2 → F) → (Fin 2 → F))
    (hsemi : ∀ (c : F) w, a (c • w) = σ c • a w) :
    Nat.card {t : F // a ![t, 0] = ![t, 0]} ≤ fixCard σ := by
  set e₀ : F := a ![1, 0] 0 with he₀
  have key : ∀ t : F, a ![t, 0] = ![t, 0] → e₀ * σ t = t := by
    intro t ht
    have h1 : (![t, 0] : Fin 2 → F) = t • (![1, 0] : Fin 2 → F) := by
      ext i
      fin_cases i <;> simp
    rw [h1, hsemi] at ht
    have := congrFun ht 0
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp only [he₀]
    simpa [mul_comm] using this
  refine (Nat.card_le_card_of_injective
    (fun t : {t : F // a ![t, 0] = ![t, 0]} => (⟨t.1, key t.1 t.2⟩ : {t : F // e₀ * σ t = t}))
    (fun x y hxy => Subtype.ext
      (congrArg (fun z : {t : F // e₀ * σ t = t} => (z : F)) hxy))).trans
    (card_twist_fixed_le σ e₀)

theorem card_eq_fixCard_pow [Finite F] (σ : F ≃+* F) : Nat.card F = fixCard σ ^ orderOf σ := by
  have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  have e : Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F) = fixCard σ :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_fixedSubfield_zpowers_iff σ x)
  rw [← e]
  exact h

end Field

variable {G : Type} [Group G] [Finite G]

namespace CoordData

variable {L M : Subgroup G} {n : ℕ} (H : CoordData G L M n)

@[expose] noncomputable def vec (w : Fin 2 → Fq n) : G := Classical.choose (H.D.exists_ψe w)

theorem vec_mem (w : Fin 2 → Fq n) : H.vec w ∈ blockU L :=
  (Classical.choose_spec (H.D.exists_ψe w)).1

theorem ψe_vec (w : Fin 2 → Fq n) : H.D.ψe (H.vec w) = w :=
  (Classical.choose_spec (H.D.exists_ψe w)).2

include H in
theorem conj_mem_blockZ {m z : G} (hm : m ∈ M) (hz : z ∈ blockZ L) : m * z * m⁻¹ ∈ blockZ L :=
  ⟨conj_mem_blockU (H.normal hm) hz.1,
    (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (H.normal hm)) z).1 hz.2⟩

include H in
theorem ψe_conj_congr {m : G} (hm : m ∈ M) {v v' : G} (hv : v ∈ blockU L) (hv' : v' ∈ blockU L)
    (h : H.D.ψe v = H.D.ψe v') : H.D.ψe (m * v * m⁻¹) = H.D.ψe (m * v' * m⁻¹) := by
  have hz : v⁻¹ * v' ∈ blockZ L := by
    refine (H.D.ψe_eq_zero_iff (mul_mem (inv_mem hv) hv')).1 ?_
    rw [H.D.ψe_mul (inv_mem hv) hv', H.D.ψe_inv hv, h]
    abel
  have hzc := H.conj_mem_blockZ hm hz
  have e : m * v' * m⁻¹ = (m * v * m⁻¹) * (m * (v⁻¹ * v') * m⁻¹) := by group
  rw [e, H.D.ψe_mul (conj_mem_blockU (H.normal hm) hv) (conj_mem_blockU (H.normal hm)
    (blockZ_le_blockU L hz)), (H.D.ψe_eq_zero_iff (blockZ_le_blockU L hzc)).2 hzc, add_zero]

@[expose] noncomputable def act (m : G) (w : Fin 2 → Fq n) : Fin 2 → Fq n :=
  H.D.ψe (m * H.vec w * m⁻¹)

theorem act_ψe {m : G} (hm : m ∈ M) {v : G} (hv : v ∈ blockU L) :
    H.act m (H.D.ψe v) = H.D.ψe (m * v * m⁻¹) :=
  H.ψe_conj_congr hm (H.vec_mem _) hv (H.ψe_vec _)

theorem act_add {m : G} (hm : m ∈ M) (w w' : Fin 2 → Fq n) :
    H.act m (w + w') = H.act m w + H.act m w' := by
  have h1 : w + w' = H.D.ψe (H.vec w * H.vec w') := by
    rw [H.D.ψe_mul (H.vec_mem w) (H.vec_mem w'), H.ψe_vec, H.ψe_vec]
  rw [h1, H.act_ψe hm (mul_mem (H.vec_mem w) (H.vec_mem w'))]
  have e : m * (H.vec w * H.vec w') * m⁻¹ = (m * H.vec w * m⁻¹) * (m * H.vec w' * m⁻¹) := by
    group
  rw [e, H.D.ψe_mul (conj_mem_blockU (H.normal hm) (H.vec_mem w))
    (conj_mem_blockU (H.normal hm) (H.vec_mem w'))]
  rfl

theorem act_one (w : Fin 2 → Fq n) : H.act 1 w = w := by
  unfold act
  rw [one_mul, inv_one, mul_one, H.ψe_vec]

theorem act_mul {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) (w : Fin 2 → Fq n) :
    H.act (m * m') w = H.act m (H.act m' w) := by
  have h1 : H.act m' w = H.D.ψe (m' * H.vec w * m'⁻¹) := rfl
  rw [h1, H.act_ψe hm (conj_mem_blockU (H.normal hm') (H.vec_mem w))]
  unfold act
  congr 1
  group

theorem act_inv_act {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) : H.act m⁻¹ (H.act m w) = w := by
  rw [← H.act_mul (M.inv_mem hm) hm, inv_mul_cancel, H.act_one]

theorem act_act_inv {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) : H.act m (H.act m⁻¹ w) = w := by
  rw [← H.act_mul hm (M.inv_mem hm), mul_inv_cancel, H.act_one]

@[expose] noncomputable def actPerm (m : ↥M) : Equiv.Perm (Fin 2 → Fq n) where
  toFun := H.act m
  invFun := H.act (m : G)⁻¹
  left_inv w := H.act_inv_act m.2 w
  right_inv w := H.act_act_inv m.2 w

@[expose] noncomputable def actHom : ↥M →* Equiv.Perm (Fin 2 → Fq n) where
  toFun := H.actPerm
  map_one' := Equiv.ext fun w => H.act_one w
  map_mul' m m' := Equiv.ext fun w => H.act_mul m.2 m'.2 w

theorem actHom_apply (m : ↥M) (w : Fin 2 → Fq n) : H.actHom m w = H.act m w := rfl

theorem actHom_add (m : ↥M) (w w' : Fin 2 → Fq n) :
    H.actHom m (w + w') = H.actHom m w + H.actHom m w' := H.act_add m.2 w w'

theorem act_L {l : G} (hl : l ∈ L) (w : Fin 2 → Fq n) :
    H.act l w = ((H.D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w := by
  unfold act
  rw [H.D.ψe_conj hl (H.vec_mem w), H.ψe_vec]

theorem actHom_L (l : ↥L) : H.actHom ⟨l, H.le l.2⟩ = slPerm (Fq n) (H.D.φ l) := by
  refine Equiv.ext fun w => ?_
  rw [H.actHom_apply, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  exact H.act_L l.2 w

theorem normalizes (m : ↥M) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    ∃ g' : Matrix.SpecialLinearGroup (Fin 2) (Fq n),
      (H.actHom m)⁻¹ * slPerm (Fq n) g * H.actHom m = slPerm (Fq n) g' := by
  set l : ↥L := H.D.sec g with hl
  have hm' : (m : G)⁻¹ * (l : G) * (m : G) ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (H.normal (M.inv_mem m.2)) (l : G)).1 l.2
    simpa using this
  refine ⟨H.D.φ ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩, ?_⟩
  rw [← H.actHom_L ⟨(m : G)⁻¹ * (l : G) * (m : G), hm'⟩]
  have e1 : (⟨(m : G)⁻¹ * (l : G) * (m : G), H.le hm'⟩ : ↥M) =
      m⁻¹ * ⟨(l : G), H.le l.2⟩ * m := Subtype.ext (by simp)
  have e2 : slPerm (Fq n) g = H.actHom ⟨(l : G), H.le l.2⟩ := by
    rw [H.actHom_L, hl, H.D.φ_sec]
  rw [e2, e1, map_mul, map_mul, map_inv]

theorem exists_sigma (m : ↥M) : ∃ σ : Fq n ≃+* Fq n, IsSemilinearWith (H.actHom m) σ :=
  exists_isSemilinearWith_of_normalizes (H.actHom m) (H.actHom_add m) (H.normalizes m)

@[expose] noncomputable def sigma (m : ↥M) : Fq n ≃+* Fq n := Classical.choose (H.exists_sigma m)

theorem isSemilinear_sigma (m : ↥M) : IsSemilinearWith (H.actHom m) (H.sigma m) :=
  Classical.choose_spec (H.exists_sigma m)

theorem sigma_unique {m : ↥M} {σ : Fq n ≃+* Fq n} (h : IsSemilinearWith (H.actHom m) σ) :
    σ = H.sigma m :=
  h.unique (H.isSemilinear_sigma m)

@[expose] noncomputable def chi : ↥M →* (Fq n ≃+* Fq n) where
  toFun := H.sigma
  map_one' := by
    symm
    exact H.sigma_unique (m := 1) (by rw [map_one]; exact IsSemilinearWith.one_perm)
  map_mul' a b := by
    symm
    exact H.sigma_unique (m := a * b)
      (by rw [map_mul]; exact (H.isSemilinear_sigma a).mul (H.isSemilinear_sigma b))

theorem chi_apply (m : ↥M) : H.chi m = H.sigma m := rfl

theorem isSemilinear_chi (m : ↥M) : IsSemilinearWith (H.actHom m) (H.chi m) :=
  H.isSemilinear_sigma m

theorem act_smul {m : G} (hm : m ∈ M) (c : Fq n) (w : Fin 2 → Fq n) :
    H.act m (c • w) = H.chi ⟨m, hm⟩ c • H.act m w :=
  H.isSemilinear_chi ⟨m, hm⟩ c w

theorem chi_eq_one_iff (m : ↥M) :
    H.chi m = 1 ↔ IsSemilinearWith (H.actHom m) (1 : Fq n ≃+* Fq n) :=
  ⟨fun h => h ▸ H.isSemilinear_chi m, fun h => (H.sigma_unique h).symm⟩

end CoordData

omit [Finite G] in
theorem conj_mem_Qc {M : Subgroup G} {L : Subgroup G} (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {m u : G} (hm : m ∈ M) (hu : u ∈ Qc L M) : m * u * m⁻¹ ∈ Qc L M :=
  (Subgroup.mem_normalizer_iff.1 (NatBlock.le_normalizer_centralizer hMN hm) u).1 hu

omit [Finite G] in
theorem relIndex_eq_card_map {A : Type} [Group A] (Q : Subgroup G) (f : ↥Q →* A)
    (X K : Subgroup G) (hXQ : X ≤ Q)
    (hK : ∀ (u : G) (hu : u ∈ Q), u ∈ X → (f ⟨u, hu⟩ = 1 ↔ u ∈ K)) :
    (K ⊓ X).relIndex X = Nat.card ((X.subgroupOf Q).map f) := by
  have h1 := Subgroup.relIndex_ker (K := X.subgroupOf Q) f
  rw [← h1]
  have h2 : f.ker ⊓ X.subgroupOf Q = (K ⊓ X).subgroupOf Q := by
    ext ⟨u, hu⟩
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(hK u hu h2).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hK u hu h2).2 h1, h2⟩
  calc (K ⊓ X).relIndex X = ((K ⊓ X).subgroupOf Q).relIndex (X.subgroupOf Q) :=
        (Subgroup.relIndex_subgroupOf hXQ).symm
    _ = (f.ker ⊓ X.subgroupOf Q).relIndex (X.subgroupOf Q) := by rw [h2]
    _ = f.ker.relIndex (X.subgroupOf Q) := Subgroup.inf_relIndex_right _ _

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem conj_mem_L {m l : G} (hm : m ∈ M) (hl : l ∈ L) : m * l * m⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.1 (H.normal hm) l).1 hl

theorem act_mulVec {m l : G} (hm : m ∈ M) (hl : l ∈ L) (w : Fin 2 → Fq n) :
    H.act m (((H.D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w) =
    ((H.D.φ ⟨m * l * m⁻¹, H.conj_mem_L hm hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec (H.act m w) := by
  have h1 : ((H.D.φ ⟨l, hl⟩ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
      Matrix (Fin 2) (Fin 2) (Fq n)).mulVec w = H.D.ψe (l * H.vec w * l⁻¹) := by
    rw [H.D.ψe_conj hl (H.vec_mem w), H.ψe_vec]
  rw [h1, H.act_ψe hm (conj_mem_blockU (Subgroup.le_normalizer hl) (H.vec_mem w))]
  have e : m * (l * H.vec w * l⁻¹) * m⁻¹ =
      (m * l * m⁻¹) * (m * H.vec w * m⁻¹) * (m * l * m⁻¹)⁻¹ := by group
  rw [e, H.D.ψe_conj (H.conj_mem_L hm hl) (conj_mem_blockU (H.normal hm) (H.vec_mem w))]
  rfl

@[expose] noncomputable def uMatHom (n : ℕ) : Multiplicative (Fq n) →* SL2 (Fq n) where
  toFun a := uMat (Multiplicative.toAdd a)
  map_one' := by simpa using uMat_zero
  map_mul' a b := by simp [uMat_mul]

theorem uMat_injective : Function.Injective (fun s : Fq n => (uMat s : SL2 (Fq n))) := by
  intro a b hab
  have := congrArg (fun g : SL2 (Fq n) => (g : Matrix (Fin 2) (Fin 2) (Fq n)) 0 1) hab
  simpa [uMat_coe] using this

theorem exists_mem_Rl_phi_eq_uMat (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T)
    (s : Fq n) : ∃ (r : G) (hr : r ∈ L), r ∈ T ∧ H.D.φ ⟨r, hr⟩ = uMat s := by
  classical
  have hn : n ≠ 0 := H.n_ne_zero
  let f : ↥(Rl L T) →* SL2 (Fq n) := H.D.φ.comp (Subgroup.inclusion Rl_le_L)
  have hu_inj : Function.Injective (uMatHom n) := fun a b hab => by
    exact Multiplicative.toAdd.injective (uMat_injective hab)
  have hrange_le : f.range ≤ (uMatHom n).range := by
    rintro _ ⟨r, rfl⟩
    obtain ⟨s', hs'⟩ := hA r.1 (Rl_le_L r.2) r.2.1
    exact ⟨Multiplicative.ofAdd s', hs'.symm⟩
  have hWR : oTwoIn L ≤ Rl L T :=
    le_inf (NatBlock.oTwoIn_le_sylow H.le H.normal hT) (oTwoIn_le L)
  have hker : f.ker = (oTwoIn L).subgroupOf (Rl L T) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact H.D.φ_ker ⟨r.1, Rl_le_L r.2⟩
  have hkcard : Nat.card f.ker = Nat.card (oTwoIn L) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range f
  have hcardR := card_Rl H.nat H.le H.normal hT
  have hpos : 0 < Nat.card (oTwoIn L) := Nat.card_pos
  have hrange_card : Nat.card f.range = 2 ^ n := by
    have hkpos : 0 < Nat.card f.ker := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hkpos
    rw [hmul, hcardR, hkcard]
    ring
  have hur : Nat.card (uMatHom n).range = 2 ^ n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hu_inj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fq n) ≃ _)]
    exact GaloisField.card 2 n hn
  have heq : f.range = (uMatHom n).range :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hur, hrange_card])
  have hs : uMat s ∈ (uMatHom n).range := ⟨Multiplicative.ofAdd s, rfl⟩
  rw [← heq] at hs
  obtain ⟨r, hr⟩ := hs
  exact ⟨r.1, Rl_le_L r.2, r.2.1, hr⟩

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

theorem act_zero {m : G} (hm : m ∈ M) : H.act m 0 = 0 := by
  have := H.act_add hm 0 0
  simpa using this

theorem act_apply_eq {m : G} (hm : m ∈ M) (w : Fin 2 → Fq n) :
    H.act m w = H.chi ⟨m, hm⟩ (w 0) • H.act m ![1, 0] + H.chi ⟨m, hm⟩ (w 1) • H.act m ![0, 1] := by
  have h := semilinear_apply (σ := H.chi ⟨m, hm⟩) (a := H.act m) (H.act_add hm)
    (fun c w => H.act_smul hm c w) w
  have e0 : (Pi.single 0 1 : Fin 2 → Fq n) = ![1, 0] := by
    ext i
    fin_cases i <;> simp
  have e1 : (Pi.single 1 1 : Fin 2 → Fq n) = ![0, 1] := by
    ext i
    fin_cases i <;> simp
  rwa [e0, e1] at h

include H in
theorem act_uMat_rel {x : G} (hx : x ∈ M) {r : G} (hr : r ∈ L) {s t : Fq n}
    (hs : H.D.φ ⟨r, hr⟩ = uMat s) (ht : H.D.φ ⟨x * r * x⁻¹, H.conj_mem_L hx hr⟩ = uMat t) :
    H.chi ⟨x, hx⟩ s * H.act x ![1, 0] 0 = t * H.act x ![0, 1] 1 ∧
      H.chi ⟨x, hx⟩ s * H.act x ![1, 0] 1 = 0 := by
  have h := H.act_mulVec hx hr ![0, 1]
  rw [hs, ht] at h
  have e1 : ((uMat s : SL2 (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)).mulVec ![0, 1] =
      s • (![1, 0] : Fin 2 → Fq n) + ![0, 1] := by
    ext i
    fin_cases i <;> simp [uMat_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e1, H.act_add hx, H.act_smul hx] at h
  have e2 := congrFun h 0
  have e3 := congrFun h 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, uMat_coe, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at e2 e3
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, one_mul, zero_add] at e2 e3
  refine ⟨?_, ?_⟩
  · linear_combination e2
  · linear_combination e3

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

theorem act_line (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) :
    H.act x ![1, 0] 1 = 0 ∧ H.act x ![0, 1] 1 ≠ 0 ∧ H.act x ![1, 0] 0 ≠ 0 := by
  have hxM : x ∈ M := hT.le hx
  obtain ⟨r, hr, hrT, hrφ⟩ := H.exists_mem_Rl_phi_eq_uMat hT hA 1
  obtain ⟨t, ht⟩ := hA (x * r * x⁻¹) (H.conj_mem_L hxM hr)
    (T.mul_mem (T.mul_mem hx hrT) (T.inv_mem hx))
  have hrel := H.act_uMat_rel hxM hr hrφ ht
  have he1 : H.act x ![1, 0] 1 = 0 := by
    have := hrel.2
    rwa [map_one, one_mul] at this
  refine ⟨he1, ?_, ?_⟩
  · intro hf1
    have h := H.act_apply_eq hxM (H.act x⁻¹ ![0, 1])
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he1, hf1, mul_zero, add_zero] at h1
    rw [H.act_act_inv hxM] at h1
    simp at h1
  · intro he0
    have he : H.act x ![1, 0] = 0 := by
      ext i
      fin_cases i
      · exact he0
      · exact he1
    have hinj : (![1, 0] : Fin 2 → Fq n) = 0 := by
      have := congrArg (H.act x⁻¹) he
      rw [H.act_inv_act hxM, H.act_zero (M.inv_mem hxM)] at this
      exact this
    have := congrFun hinj 0
    simp at this

end CoordData

section Sqrt

theorem sigma_sqrtF {F : Type} [Field F] [Fintype F] [CharP F 2] (σ : F ≃+* F) (t : F) :
    σ (sqrtF t) = sqrtF (σ t) := by
  apply sq_inj
  rw [sqrtF_sq, ← map_pow, sqrtF_sq]

end Sqrt

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem eq_zero_of_forall_add_sqrt {A B : Fq n} (h : ∀ s : Fq n, A * s + B * sqrtF s = 0) :
    A = 0 ∧ B = 0 := by
  classical
  have h1 := h 1
  rw [sqrtF_one, mul_one, mul_one] at h1
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset (Fq n))) (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt Finset.card_le_two H.two_lt_card)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc₀
  have h2 := h (c₀ ^ 2)
  rw [sqrtF_of_sq] at h2
  have h3 : A * (c₀ * (c₀ - 1)) = 0 := by linear_combination h2 - c₀ * h1
  have hA : A = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hc₀.1
      · exact absurd (sub_eq_zero.1 h) hc₀.2
  refine ⟨hA, ?_⟩
  rw [hA, zero_add] at h1
  exact h1

include H in
theorem psi_delta_conj {x : G} (hx : x ∈ M) {u l : G} (hu : u ∈ Qc L M) (hl : l ∈ L) :
    H.D.ψe (delta (x * u * x⁻¹) l) = H.act x (H.D.ψe (delta u (x⁻¹ * l * x))) := by
  have hl' : x⁻¹ * l * x ∈ L := by
    have := H.conj_mem_L (M.inv_mem hx) hl
    simpa using this
  have hV : delta u (x⁻¹ * l * x) ∈ blockU L := H.nat.delta_mem H.normal hu hl'
  rw [H.act_ψe hx hV]
  congr 1
  simp only [delta]
  group

include H in
theorem theta_conj (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) :
    ∃ ν : Fq n, ∀ (u : G) (hu : u ∈ Qc L M),
      H.theta ⟨x * u * x⁻¹, conj_mem_Qc H.normal (hT.le hx) hu⟩ =
        ν * H.chi ⟨x, hT.le hx⟩ (H.theta ⟨u, hu⟩) := by
  have hxM : x ∈ M := hT.le hx
  obtain ⟨he1, hf1, he0⟩ := H.act_line hT hA hx
  set e0 := H.act x ![1, 0] 0 with he0def
  set f1 := H.act x ![0, 1] 1 with hf1def
  set σ := H.chi ⟨x, hxM⟩ with hσ
  refine ⟨e0 * sqrtF (f1 / e0), fun u hu => ?_⟩
  have hu' := conj_mem_Qc H.normal hxM hu
  have key : ∀ s : Fq n, (H.vco ⟨x * u * x⁻¹, hu'⟩ 1 - f1 * σ (H.vco ⟨u, hu⟩ 1)) * s +
      (H.theta ⟨x * u * x⁻¹, hu'⟩ - e0 * sqrtF (f1 / e0) * σ (H.theta ⟨u, hu⟩)) * sqrtF s = 0 := by
    intro s
    obtain ⟨l, hl, hlT, hlφ⟩ := H.exists_mem_Rl_phi_eq_uMat hT hA s
    have hrL : x⁻¹ * l * x ∈ L := by
      have := H.conj_mem_L (M.inv_mem hxM) hl
      simpa using this
    have hrT : x⁻¹ * l * x ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hx) hlT) hx
    obtain ⟨t, ht⟩ := hA (x⁻¹ * l * x) hrL hrT
    have ht' : H.D.φ ⟨x * (x⁻¹ * l * x) * x⁻¹, H.conj_mem_L hxM hrL⟩ = uMat s := by
      have : (⟨x * (x⁻¹ * l * x) * x⁻¹, H.conj_mem_L hxM hrL⟩ : ↥L) = ⟨l, hl⟩ :=
        Subtype.ext (by group)
      rw [this]
      exact hlφ
    obtain ⟨h1, -⟩ := H.act_uMat_rel hxM hrL ht ht'
    have hψ := H.psi_delta_conj hxM hu hl
    have hψ1 : H.D.ψe (delta (x * u * x⁻¹) l) =
        ![s * H.vco ⟨x * u * x⁻¹, hu'⟩ 1 + H.theta ⟨x * u * x⁻¹, hu'⟩ * sqrtF s, 0] :=
      H.ψe_delta_uMat ⟨x * u * x⁻¹, hu'⟩ hl hlφ
    have hψ2 : H.D.ψe (delta u (x⁻¹ * l * x)) =
        ![t * H.vco ⟨u, hu⟩ 1 + H.theta ⟨u, hu⟩ * sqrtF t, 0] :=
      H.ψe_delta_uMat ⟨u, hu⟩ hrL ht
    rw [hψ1, hψ2, H.act_apply_eq hxM] at hψ
    have hcomp := congrFun hψ 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at hcomp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, zero_mul, add_zero] at hcomp
    have hσt : σ t = s * (f1 / e0) := by
      field_simp
      linear_combination h1
    rw [map_add, map_mul, map_mul, sigma_sqrtF, hσt, sqrtF_mul] at hcomp
    have hq : f1 / e0 * e0 = f1 := by field_simp
    linear_combination hcomp + (s * σ (H.vco ⟨u, hu⟩ 1)) * hq
  have := (H.eq_zero_of_forall_add_sqrt key).2
  exact sub_eq_zero.1 this

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem vco_conj_of_theta_eq_zero {x : G} (hx : x ∈ M) {u : G} (hu : u ∈ Qc L M)
    (hθ : H.theta ⟨u, hu⟩ = 0) :
    H.vco ⟨x * u * x⁻¹, conj_mem_Qc H.normal hx hu⟩ = H.act x (H.vco ⟨u, hu⟩) ∧
      H.theta ⟨x * u * x⁻¹, conj_mem_Qc H.normal hx hu⟩ = 0 := by
  obtain ⟨v, hv, hψ, hc⟩ := H.exists_blockU_of_theta_eq_zero ⟨u, hu⟩ hθ
  have hvQ : v ∈ Qc L M := H.blockU_le_Qc hv
  have hxvQ : x * v * x⁻¹ ∈ Qc L M := conj_mem_Qc H.normal hx hvQ
  have hxv : x * v * x⁻¹ ∈ blockU L := conj_mem_blockU (H.normal hx) hv
  have hxu := conj_mem_Qc H.normal hx hu
  have hcL : (x * u * x⁻¹) * (x * v * x⁻¹)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have e : (x * u * x⁻¹) * (x * v * x⁻¹)⁻¹ = x * (u * v⁻¹) * x⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (mem_normalizer_centralizer (H.normal hx)) _).1 hc
  have hco := H.coords_eq_of_mul_inv_mem (u := ⟨x * u * x⁻¹, hxu⟩) (u' := ⟨x * v * x⁻¹, hxvQ⟩) hcL
  have hv' := H.vco_blockU hxv
  refine ⟨?_, ?_⟩
  · rw [hco.1, hv'.1, ← hψ, H.act_ψe hx hv]
  · rw [hco.2, hv'.2]

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem Rl_le_normalizer_Dc (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Rl L T ≤ Subgroup.normalizer (Dc L T : Set G) :=
  Rl_le_T.trans (le_normalizer_Dc H.normal hT.le)

include H in
theorem exists_param (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {y : G}
    (hy : y ∈ Rl L T ⊔ Dc L T) :
    ∃ (s : Fq n) (r d : G) (hr : r ∈ L), r ∈ T ∧ d ∈ Dc L T ∧ y = r * d ∧
      H.D.φ ⟨r, hr⟩ = uMat s := by
  obtain ⟨r, hr, d, hd, rfl⟩ := (Aux.mem_sup_iff_mul (H.Rl_le_normalizer_Dc hT)).1 hy
  obtain ⟨s, hs⟩ := hA r hr.2 hr.1
  exact ⟨s, r, d, hr.2, hr.1, hd, rfl, hs⟩

include H in
theorem param_unique (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {r d r' d' : G} (hr : r ∈ L)
    (hr' : r' ∈ L) (hrT : r ∈ T) (hrT' : r' ∈ T) (hd : d ∈ Dc L T) (hd' : d' ∈ Dc L T)
    (h : r * d = r' * d') {s s' : Fq n} (hs : H.D.φ ⟨r, hr⟩ = uMat s)
    (hs' : H.D.φ ⟨r', hr'⟩ = uMat s') : s = s' := by
  have e : r⁻¹ * r' = d * d'⁻¹ := by
    calc r⁻¹ * r' = r⁻¹ * (r' * d') * d'⁻¹ := by group
      _ = r⁻¹ * (r * d) * d'⁻¹ := by rw [h]
      _ = d * d'⁻¹ := by group
  have hW : r⁻¹ * r' ∈ oTwoIn L := by
    rw [← Rl_inf_Dc H.nat H.le H.normal hT]
    refine ⟨⟨T.mul_mem (T.inv_mem hrT) hrT', L.mul_mem (L.inv_mem hr) hr'⟩, ?_⟩
    rw [e]
    exact (Dc L T).mul_mem hd ((Dc L T).inv_mem hd')
  have h1 := (H.D.φ_ker ⟨r⁻¹ * r', L.mul_mem (L.inv_mem hr) hr'⟩).2 hW
  have e2 : (⟨r⁻¹ * r', L.mul_mem (L.inv_mem hr) hr'⟩ : ↥L) = (⟨r, hr⟩ : ↥L)⁻¹ * ⟨r', hr'⟩ := rfl
  rw [e2, map_mul, map_inv, hs, hs', inv_mul_eq_one] at h1
  exact uMat_injective h1

open Classical in
@[expose] noncomputable def rhoBar (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T)
    (y : G) : Fq n :=
  if h : y ∈ Rl L T ⊔ Dc L T then Classical.choose (H.exists_param hT hA h) else 0

include H in
theorem rhoBar_eq (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {r d : G}
    (hr : r ∈ L) (hrT : r ∈ T) (hd : d ∈ Dc L T) {s : Fq n} (hs : H.D.φ ⟨r, hr⟩ = uMat s) :
    H.rhoBar hT hA (r * d) = s := by
  have hy : r * d ∈ Rl L T ⊔ Dc L T :=
    mul_mem (Subgroup.mem_sup_left ⟨hrT, hr⟩) (Subgroup.mem_sup_right hd)
  simp only [rhoBar, hy, ↓reduceDIte]
  obtain ⟨r', d', hr', hrT', hd', hy', hs'⟩ := Classical.choose_spec (H.exists_param hT hA hy)
  exact (H.param_unique hT hr' hr hrT' hrT hd' hd hy'.symm hs' hs)

include H in
theorem rhoBar_mul (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {y y' : G}
    (hy : y ∈ Rl L T ⊔ Dc L T) (hy' : y' ∈ Rl L T ⊔ Dc L T) :
    H.rhoBar hT hA (y * y') = H.rhoBar hT hA y + H.rhoBar hT hA y' := by
  obtain ⟨s, r, d, hr, hrT, hd, rfl, hs⟩ := H.exists_param hT hA hy
  obtain ⟨s', r', d', hr', hrT', hd', rfl, hs'⟩ := H.exists_param hT hA hy'
  have hd'' : r'⁻¹ * d * r' ∈ Dc L T := by
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dc H.normal hT.le (T.inv_mem hrT')) d).1
      hd
    simpa using this
  have e : r * d * (r' * d') = (r * r') * ((r'⁻¹ * d * r') * d') := by group
  have hrr : H.D.φ ⟨r * r', L.mul_mem hr hr'⟩ = uMat (s + s') := by
    have e2 : (⟨r * r', L.mul_mem hr hr'⟩ : ↥L) = ⟨r, hr⟩ * ⟨r', hr'⟩ := rfl
    rw [e2, map_mul, hs, hs', uMat_mul]
  rw [e, H.rhoBar_eq hT hA (L.mul_mem hr hr') (T.mul_mem hrT hrT') ((Dc L T).mul_mem hd'' hd')
    hrr, H.rhoBar_eq hT hA hr hrT hd hs, H.rhoBar_eq hT hA hr' hrT' hd' hs']

include H in
theorem rhoBar_eq_zero_iff (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {y : G}
    (hy : y ∈ Rl L T ⊔ Dc L T) : H.rhoBar hT hA y = 0 ↔ y ∈ Dc L T := by
  obtain ⟨s, r, d, hr, hrT, hd, rfl, hs⟩ := H.exists_param hT hA hy
  rw [H.rhoBar_eq hT hA hr hrT hd hs]
  constructor
  · rintro rfl
    have hφ : H.D.φ ⟨r, hr⟩ = 1 := by rw [hs, uMat_zero]
    have hW := (H.D.φ_ker ⟨r, hr⟩).1 hφ
    exact (Dc L T).mul_mem (oTwoIn_le_Dc H.nat H.le H.normal hT hW) hd
  · intro hrd
    have hrD : r ∈ Dc L T := by
      have := (Dc L T).mul_mem hrd ((Dc L T).inv_mem hd)
      simpa using this
    have hW : r ∈ oTwoIn L := by
      rw [← Rl_inf_Dc H.nat H.le H.normal hT]
      exact ⟨⟨hrT, hr⟩, hrD⟩
    have h1 := (H.D.φ_ker ⟨r, hr⟩).2 hW
    rw [hs] at h1
    have : uMat s = uMat (0 : Fq n) := by rw [h1, uMat_zero]
    exact uMat_injective this

end CoordData

omit [Finite G] in
theorem card_map_le {A F : Type} [Group A] [AddCommGroup F] [Finite F] (K : Subgroup A)
    (f : A →* Multiplicative F) (P : F → Prop)
    (hP : ∀ k ∈ K, P (Multiplicative.toAdd (f k))) :
    Nat.card (K.map f) ≤ Nat.card {t : F // P t} :=
  Nat.card_le_card_of_injective
    (fun p : K.map f => (⟨Multiplicative.toAdd p.1, by
      obtain ⟨k, hk, hkp⟩ := p.2
      rw [← hkp]
      exact hP k hk⟩ : {t : F // P t}))
    (fun p q h => Subtype.ext (Multiplicative.toAdd.injective
      (congrArg (fun z : {t : F // P t} => (z : F)) h)))

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

@[expose] noncomputable def rhoHom (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) :
    ↥(Rl L T ⊔ Dc L T) →* Multiplicative (Fq n) :=
  MonoidHom.mk' (fun y => Multiplicative.ofAdd (H.rhoBar hT hA y)) (fun a b => by
    simp only [Subgroup.coe_mul]
    rw [H.rhoBar_mul hT hA a.2 b.2, ofAdd_add])

include H in
theorem rhoBar_conj (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) {y : G} (hy : y ∈ Rl L T ⊔ Dc L T) :
    H.rhoBar hT hA (x * y * x⁻¹) * H.act x ![0, 1] 1 =
      H.chi ⟨x, hT.le hx⟩ (H.rhoBar hT hA y) * H.act x ![1, 0] 0 := by
  obtain ⟨s, r, d, hr, hrT, hd, rfl, hs⟩ := H.exists_param hT hA hy
  have hxM := hT.le hx
  have hxrL : x * r * x⁻¹ ∈ L := H.conj_mem_L hxM hr
  have hxrT : x * r * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hrT) (T.inv_mem hx)
  obtain ⟨t, ht⟩ := hA _ hxrL hxrT
  have hxd : x * d * x⁻¹ ∈ Dc L T :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_Dc H.normal hT.le hx) d).1 hd
  have e : x * (r * d) * x⁻¹ = (x * r * x⁻¹) * (x * d * x⁻¹) := by group
  rw [e, H.rhoBar_eq hT hA hxrL hxrT hxd ht, H.rhoBar_eq hT hA hr hrT hd hs]
  exact (H.act_uMat_rel hxM hr hs ht).1.symm

include H in
theorem relIndex_Dc_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) {X : Subgroup G} (hX : X ≤ Rl L T ⊔ Dc L T)
    (hxX : ∀ y ∈ X, x * y = y * x) :
    (Dc L T ⊓ X).relIndex X ≤ fixCard (H.chi ⟨x, hT.le hx⟩) := by
  obtain ⟨he1, hf1, he0⟩ := H.act_line hT hA hx
  have h1 := relIndex_eq_card_map (Rl L T ⊔ Dc L T) (H.rhoHom hT hA) X (Dc L T) hX
    (fun u hu _ => by
      show Multiplicative.ofAdd (H.rhoBar hT hA u) = 1 ↔ _
      rw [ofAdd_eq_one]
      exact H.rhoBar_eq_zero_iff hT hA hu)
  rw [h1]
  refine (card_map_le (X.subgroupOf (Rl L T ⊔ Dc L T)) (H.rhoHom hT hA)
    (fun t => H.act x ![1, 0] 0 / H.act x ![0, 1] 1 * H.chi ⟨x, hT.le hx⟩ t = t) ?_).trans
    (card_twist_fixed_le _ _)
  rintro ⟨y, hy⟩ hyX
  have hyX' : y ∈ X := hyX
  have hc := H.rhoBar_conj hT hA hx hy
  have hxy : x * y * x⁻¹ = y := by
    rw [hxX y hyX']
    group
  rw [hxy] at hc
  show H.act x ![1, 0] 0 / H.act x ![0, 1] 1 * H.chi ⟨x, hT.le hx⟩ (H.rhoBar hT hA y) =
    H.rhoBar hT hA y
  field_simp
  linear_combination -hc

end CoordData

omit [Finite G] in
theorem Dc_le_Qc {L M T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    Dc L T ≤ Qc L M := fun _ hx => ⟨hT.le hx.1, hx.2⟩

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

@[expose] noncomputable def thetaHom : ↥(Qc L M) →* Multiplicative (Fq n) :=
  MonoidHom.mk' (fun u => Multiplicative.ofAdd (H.theta u)) (fun u u' => by
    rw [(H.vco_mul u u').2, ofAdd_add])

@[expose] noncomputable def vcoHom : ↥(Qc L M) →* Multiplicative (Fin 2 → Fq n) :=
  MonoidHom.mk' (fun u => Multiplicative.ofAdd (H.vco u)) (fun u u' => by
    rw [(H.vco_mul u u').1, ofAdd_add])

include H in
theorem blockU_normalizes_Ec (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
  (NatBlock.blockU_le_sylow H.le H.normal hT).trans (le_normalizer_Ec H.normal hT.le)

include H in
theorem blockU_sup_Ec_le_T (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    blockU L ⊔ Ec L T ≤ T :=
  sup_le (NatBlock.blockU_le_sylow H.le H.normal hT) Ec_le_T

include H in
theorem blockU_sup_Ec_le_Dc (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    blockU L ⊔ Ec L T ≤ Dc L T :=
  sup_le (blockU_le_Dc H.nat H.le H.normal hT) Ec_le_Dc

include H in
theorem theta_eq_zero_iff_mem_sup (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {u : G}
    (hu : u ∈ Dc L T) : H.theta ⟨u, Dc_le_Qc hT hu⟩ = 0 ↔ u ∈ blockU L ⊔ Ec L T := by
  constructor
  · intro h0
    obtain ⟨v, hv, hc⟩ := (H.theta_eq_zero_iff ⟨u, Dc_le_Qc hT hu⟩).1 h0
    have hvT : v ∈ T := NatBlock.blockU_le_sylow H.le H.normal hT hv
    have hE : u * v⁻¹ ∈ Ec L T := ⟨T.mul_mem hu.1 (T.inv_mem hvT), hc⟩
    have e : u = (u * v⁻¹) * v := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right hE) (Subgroup.mem_sup_left hv)
  · intro hu'
    obtain ⟨v, hv, e, he, rfl⟩ := (Aux.mem_sup_iff_mul (H.blockU_normalizes_Ec hT)).1 hu'
    refine (H.theta_eq_zero_iff _).2 ⟨v, hv, ?_⟩
    have : v * e * v⁻¹ ∈ Ec L T :=
      (Subgroup.mem_normalizer_iff.1 (H.blockU_normalizes_Ec hT hv) e).1 he
    exact this.2

include H in
theorem relIndex_sup_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) {X : Subgroup G} (hXD : X ≤ Dc L T) (hxX : ∀ u ∈ X, x * u = u * x) :
    ((blockU L ⊔ Ec L T) ⊓ X).relIndex X ≤ fixCard (H.chi ⟨x, hT.le hx⟩) := by
  obtain ⟨ν, hν⟩ := H.theta_conj hT hA hx
  have hK : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ X →
      (H.thetaHom ⟨u, hu⟩ = 1 ↔ u ∈ blockU L ⊔ Ec L T) := fun u hu huX => by
    show Multiplicative.ofAdd (H.theta ⟨u, hu⟩) = 1 ↔ _
    rw [ofAdd_eq_one]
    exact H.theta_eq_zero_iff_mem_sup hT (hXD huX)
  rw [relIndex_eq_card_map (Qc L M) H.thetaHom X _ (hXD.trans (Dc_le_Qc hT)) hK]
  refine (card_map_le (X.subgroupOf (Qc L M)) H.thetaHom
    (fun t => ν * H.chi ⟨x, hT.le hx⟩ t = t) ?_).trans (card_twist_fixed_le _ _)
  rintro ⟨u, hu⟩ huX
  have huX' : u ∈ X := huX
  have h := hν u hu
  have hxu : x * u * x⁻¹ = u := by
    rw [hxX u huX']
    group
  have e : (⟨x * u * x⁻¹, conj_mem_Qc H.normal (hT.le hx) hu⟩ : ↥(Qc L M)) = ⟨u, hu⟩ :=
    Subtype.ext hxu
  rw [e] at h
  exact h.symm

include H in
theorem relIndex_Ec_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G}
    (hx : x ∈ T) {Y : Subgroup G} (hY : Y ≤ blockU L ⊔ Ec L T)
    (hxY : ∀ u ∈ Y, x * u = u * x) :
    (Ec L T ⊓ Y).relIndex Y ≤ fixCard (H.chi ⟨x, hT.le hx⟩) ^ 2 := by
  have hYD : Y ≤ Dc L T := hY.trans (H.blockU_sup_Ec_le_Dc hT)
  have hθ : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ Y → H.theta ⟨u, hu⟩ = 0 := fun u hu huY =>
    (H.theta_eq_zero_iff_mem_sup hT (hYD huY)).2 (hY huY)
  have hK : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ Y → (H.vcoHom ⟨u, hu⟩ = 1 ↔ u ∈ Ec L T) :=
    fun u hu huY => by
      show Multiplicative.ofAdd (H.vco ⟨u, hu⟩) = 1 ↔ _
      rw [ofAdd_eq_one]
      constructor
      · intro hw
        have hu0 := (H.coords_eq_zero_iff ⟨u, hu⟩).1 ⟨hw, hθ u hu huY⟩
        exact ⟨(H.blockU_sup_Ec_le_T hT) (hY huY), hu0⟩
      · intro hE
        exact ((H.coords_eq_zero_iff ⟨u, hu⟩).2 hE.2).1
  rw [relIndex_eq_card_map (Qc L M) H.vcoHom Y _ (hYD.trans (Dc_le_Qc hT)) hK]
  refine (card_map_le (Y.subgroupOf (Qc L M)) H.vcoHom (fun w => H.act x w = w) ?_).trans ?_
  · rintro ⟨u, hu⟩ huY
    have huY' : u ∈ Y := huY
    have h := (H.vco_conj_of_theta_eq_zero (hT.le hx) hu (hθ u hu huY')).1
    have hxu : x * u * x⁻¹ = u := by
      rw [hxY u huY']
      group
    have e : (⟨x * u * x⁻¹, conj_mem_Qc H.normal (hT.le hx) hu⟩ : ↥(Qc L M)) = ⟨u, hu⟩ :=
      Subtype.ext hxu
    rw [e] at h
    exact h.symm
  · exact card_fixed_le_sq _ _ (H.act_add (hT.le hx)) (fun c w => H.act_smul (hT.le hx) c w)

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem psi_delta_eq_zero_of_comm (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {u r q : G}
    (hu : u ∈ Dc L T) (hr : r ∈ Rl L T) (hq : q ∈ Dc L T) (hcomm : r * q * u = u * (r * q)) :
    H.D.ψe (delta u r) = 0 := by
  have huQ : u ∈ Qc L M := Dc_le_Qc hT hu
  have hinv : u⁻¹ ∈ Dc L T := inv_mem hu
  have heE : u⁻¹ * q * u * q⁻¹ ∈ Ec L T := by
    have := Dc_comm_mem_Ec H.nat H.normal hT hinv hq
    simpa [commutatorElement_def] using this
  have hρe : r * (u⁻¹ * q * u * q⁻¹) = (u⁻¹ * q * u * q⁻¹) * r :=
    Subgroup.mem_centralizer_iff.1 heE.2 r hr.2
  have h1 : r * u * (u⁻¹ * q * u * q⁻¹) = u * r := by
    calc r * u * (u⁻¹ * q * u * q⁻¹) = (r * q * u) * q⁻¹ := by group
      _ = (u * (r * q)) * q⁻¹ := by rw [hcomm]
      _ = u * r := by group
  have hdel : delta u r = (u⁻¹ * q * u * q⁻¹)⁻¹ := by
    calc delta u r
        = u⁻¹ * (r * u * (u⁻¹ * q * u * q⁻¹)) * (u⁻¹ * q * u * q⁻¹)⁻¹ * r⁻¹ := by
          simp only [delta]
          group
      _ = u⁻¹ * (u * r) * (u⁻¹ * q * u * q⁻¹)⁻¹ * r⁻¹ := by rw [h1]
      _ = r * (u⁻¹ * q * u * q⁻¹)⁻¹ * r⁻¹ := by group
      _ = (u⁻¹ * q * u * q⁻¹)⁻¹ := by
        have hc : Commute r (u⁻¹ * q * u * q⁻¹) := hρe
        rw [hc.inv_right.eq]
        group
  have hVm : delta u r ∈ blockU L := H.nat.delta_mem H.normal huQ hr.2
  have hZm : delta u r ∈ blockZ L := by
    have hC : delta u r ∈ Subgroup.centralizer (L : Set G) := by
      rw [hdel]
      exact (Subgroup.centralizer (L : Set G)).inv_mem heE.2
    exact Subgroup.mem_inf.2 ⟨hVm, hC⟩
  exact (H.D.ψe_eq_zero_iff hVm).2 hZm

include H in
theorem relIndex_Ec_le_line (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) {Y : Subgroup G} (hY : Y ≤ blockU L ⊔ Ec L T)
    (hxY : ∀ u ∈ Y, x * u = u * x) {r : G} (hr : r ∈ Rl L T ⊔ Dc L T) (hrD : r ∉ Dc L T)
    (hrY : ∀ u ∈ Y, r * u = u * r) :
    (Ec L T ⊓ Y).relIndex Y ≤ fixCard (H.chi ⟨x, hT.le hx⟩) := by
  have hYD : Y ≤ Dc L T := hY.trans (H.blockU_sup_Ec_le_Dc hT)
  have hθ : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ Y → H.theta ⟨u, hu⟩ = 0 := fun u hu huY =>
    (H.theta_eq_zero_iff_mem_sup hT (hYD huY)).2 (hY huY)
  obtain ⟨s, r₀, q, hr₀L, hr₀T, hq, rfl, hs⟩ := H.exists_param hT hA hr
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hφ : H.D.φ ⟨r₀, hr₀L⟩ = 1 := by rw [hs, uMat_zero]
    exact hrD ((Dc L T).mul_mem (oTwoIn_le_Dc H.nat H.le H.normal hT
      ((H.D.φ_ker ⟨r₀, hr₀L⟩).1 hφ)) hq)
  have hw1 : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ Y → H.vco ⟨u, hu⟩ 1 = 0 := by
    intro u hu huY
    have hψ := H.psi_delta_eq_zero_of_comm hT (hYD huY) ⟨hr₀T, hr₀L⟩ hq (hrY u huY)
    rw [H.ψe_delta_uMat ⟨u, hu⟩ hr₀L hs] at hψ
    have := congrFun hψ 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply, hθ u hu huY, zero_mul, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hs0
  have hK : ∀ (u : G) (hu : u ∈ Qc L M), u ∈ Y → (H.vcoHom ⟨u, hu⟩ = 1 ↔ u ∈ Ec L T) :=
    fun u hu huY => by
      show Multiplicative.ofAdd (H.vco ⟨u, hu⟩) = 1 ↔ _
      rw [ofAdd_eq_one]
      constructor
      · intro hw
        have hu0 := (H.coords_eq_zero_iff ⟨u, hu⟩).1 ⟨hw, hθ u hu huY⟩
        exact ⟨(H.blockU_sup_Ec_le_T hT) (hY huY), hu0⟩
      · intro hE
        exact ((H.coords_eq_zero_iff ⟨u, hu⟩).2 hE.2).1
  rw [relIndex_eq_card_map (Qc L M) H.vcoHom Y _ (hYD.trans (Dc_le_Qc hT)) hK]
  have hfix : ∀ k ∈ Y.subgroupOf (Qc L M),
      H.act x (Multiplicative.toAdd (H.vcoHom k)) = Multiplicative.toAdd (H.vcoHom k) ∧
        Multiplicative.toAdd (H.vcoHom k) 1 = 0 := by
    rintro ⟨u, hu⟩ huY
    have huY' : u ∈ Y := huY
    have h := (H.vco_conj_of_theta_eq_zero (hT.le hx) hu (hθ u hu huY')).1
    have hxu : x * u * x⁻¹ = u := by
      rw [hxY u huY']
      group
    have e : (⟨x * u * x⁻¹, conj_mem_Qc H.normal (hT.le hx) hu⟩ : ↥(Qc L M)) = ⟨u, hu⟩ :=
      Subtype.ext hxu
    rw [e] at h
    exact ⟨h.symm, hw1 u hu huY'⟩
  refine le_trans (Nat.card_le_card_of_injective
    (fun p : (Y.subgroupOf (Qc L M)).map H.vcoHom => (⟨Multiplicative.toAdd p.1 0, ?_⟩ :
      {t : Fq n // H.act x ![t, 0] = ![t, 0]})) ?_) (card_line_fixed_le _ _
    (fun c w => H.act_smul (hT.le hx) c w))
  · obtain ⟨p, k, hk, rfl⟩ := p
    have h2 := hfix k hk
    have e : Multiplicative.toAdd (H.vcoHom k) = ![Multiplicative.toAdd (H.vcoHom k) 0, 0] := by
      ext i
      fin_cases i
      · rfl
      · exact h2.2
    rw [← e]
    exact h2.1
  · intro p q hpq
    obtain ⟨p, k, hk, rfl⟩ := p
    obtain ⟨q, k', hk', rfl⟩ := q
    have h1 := (hfix k hk).2
    have h1' := (hfix k' hk').2
    have h0 : Multiplicative.toAdd (H.vcoHom k) 0 = Multiplicative.toAdd (H.vcoHom k') 0 :=
      congrArg (fun z : {t : Fq n // H.act x ![t, 0] = ![t, 0]} => (z : Fq n)) hpq
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i
    · exact h0
    · exact h1.trans h1'.symm

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

theorem chi_of_mem_L {l : G} (hl : l ∈ L) : H.chi ⟨l, H.le hl⟩ = 1 := by
  refine (H.chi_eq_one_iff _).2 ?_
  have := H.actHom_L ⟨l, hl⟩
  rw [this, slPerm_eq_semilinPerm]
  exact semilinPerm_isSemilinear _ _

theorem chi_of_mem_centralizer {d : G} (hd : d ∈ Qc L M) : H.chi ⟨d, hd.1⟩ = 1 := by
  refine (H.chi_eq_one_iff _).2 ?_
  have h1 : H.actHom ⟨d, hd.1⟩ = 1 := by
    refine Equiv.ext fun w => ?_
    show H.act d w = w
    have : d * H.vec w * d⁻¹ = H.vec w := by
      have := Subgroup.mem_centralizer_iff.1 hd.2 _ (H.vec_mem w)
      calc d * H.vec w * d⁻¹ = (H.vec w * d) * d⁻¹ := by rw [this]
        _ = H.vec w := by group
    unfold act
    rw [this, H.ψe_vec]
  rw [h1]
  exact IsSemilinearWith.one_perm

include H in
theorem chi_eq_one_of_mem (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G}
    (hx : x ∈ Rl L T ⊔ Dc L T) (hxM : x ∈ M) : H.chi ⟨x, hxM⟩ = 1 := by
  obtain ⟨r, hr, d, hd, rfl⟩ := (Aux.mem_sup_iff_mul (H.Rl_le_normalizer_Dc hT)).1 hx
  have hdQ : d ∈ Qc L M := Dc_le_Qc hT hd
  have e : (⟨r * d, hxM⟩ : ↥M) = ⟨r, H.le hr.2⟩ * ⟨d, hdQ.1⟩ := rfl
  rw [e, map_mul, H.chi_of_mem_L hr.2, H.chi_of_mem_centralizer hdQ, mul_one]

include H in
theorem mem_sup_of_chi_eq_one (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G} (hx : x ∈ T)
    (h : H.chi ⟨x, hT.le hx⟩ = 1) : x ∈ Rl L T ⊔ Dc L T := by
  classical
  have hxM : x ∈ M := hT.le hx
  have hlin : IsSemilinearWith (H.actHom ⟨x, hxM⟩) (1 : Fq n ≃+* Fq n) :=
    (H.chi_eq_one_iff _).1 h
  have hadd := H.actHom_add ⟨x, hxM⟩
  set A : Matrix (Fin 2) (Fin 2) (Fq n) := columnMat (H.actHom ⟨x, hxM⟩) with hA
  have hAmul : ∀ w, A.mulVec w = H.act x w := fun w => columnMat_mulVec hadd hlin w
  have hdet : A.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have h1 : H.act x v = H.act x 0 := by rw [← hAmul, hv, H.act_zero hxM]
    have := congrArg (H.act x⁻¹) h1
    rwa [H.act_inv_act hxM, H.act_inv_act hxM] at this
  set lam : Fq n := sqrtF A.det with hlam
  have hlam2 : lam ^ 2 = A.det := sqrtF_sq _
  have hlam0 : lam ≠ 0 := fun h0 => hdet (by rw [← hlam2, h0]; ring)
  have hdet' : (lam⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hlam2]
    field_simp
  let g : SL2 (Fq n) := ⟨lam⁻¹ • A, hdet'⟩
  have hcomm : ∀ (l : G) (hl : l ∈ L),
      g * H.D.φ ⟨l, hl⟩ = H.D.φ ⟨x * l * x⁻¹, H.conj_mem_L hxM hl⟩ * g := by
    intro l hl
    have h1 : A * ((H.D.φ ⟨l, hl⟩ : SL2 (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)) =
        ((H.D.φ ⟨x * l * x⁻¹, H.conj_mem_L hxM hl⟩ : SL2 (Fq n)) :
          Matrix (Fin 2) (Fin 2) (Fq n)) * A := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun w => ?_
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [hAmul, hAmul]
      exact H.act_mulVec hxM hl w
    apply Subtype.ext
    show lam⁻¹ • A * ((H.D.φ ⟨l, hl⟩ : SL2 (Fq n)) : Matrix (Fin 2) (Fin 2) (Fq n)) =
      ((H.D.φ ⟨x * l * x⁻¹, H.conj_mem_L hxM hl⟩ : SL2 (Fq n)) :
        Matrix (Fin 2) (Fin 2) (Fq n)) * (lam⁻¹ • A)
    rw [Matrix.smul_mul, Matrix.mul_smul, h1]
  obtain ⟨l', hl'⟩ := H.D.φ_surj g
  have hy : l'.1⁻¹ * x ∈ cenW L M := by
    refine (mem_cenW_of_le H.normal).2 ⟨M.mul_mem (M.inv_mem (H.le l'.2)) hxM, fun l hl => ?_⟩
    have e : ⁅l'.1⁻¹ * x, l⁆ =
        ((l'⁻¹ * ⟨x * l * x⁻¹, H.conj_mem_L hxM hl⟩ * l' * (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    refine (H.D.φ_ker _).1 ?_
    have h2 := hcomm l hl
    simp only [map_mul, map_inv, hl']
    have h3 : H.D.φ ⟨x * l * x⁻¹, H.conj_mem_L hxM hl⟩ = g * H.D.φ ⟨l, hl⟩ * g⁻¹ := by
      rw [h2]
      group
    rw [h3]
    group
  have hxK : x ∈ L ⊔ cenW L M := by
    have e : x = l'.1 * (l'.1⁻¹ * x) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left l'.2) (Subgroup.mem_sup_right hy)
  rw [← inf_sup_cenW H.nat H.le H.normal hT]
  exact ⟨hx, hxK⟩

include H in
theorem chi_eq_one_iff_mem (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G} (hx : x ∈ T) :
    H.chi ⟨x, hT.le hx⟩ = 1 ↔ x ∈ Rl L T ⊔ Dc L T :=
  ⟨H.mem_sup_of_chi_eq_one hT hx, fun h => H.chi_eq_one_of_mem hT h _⟩

end CoordData

section Order

variable {F : Type} [Field F] [Finite F]

theorem two_le_orderOf {σ : F ≃+* F} (hσ : σ ≠ 1) : 2 ≤ orderOf σ := by
  have h := card_eq_fixCard_pow σ
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have h0 : orderOf σ ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at h
    omega
  have h2 : orderOf σ ≠ 1 := fun h' => hσ (orderOf_eq_one_iff.1 h')
  omega

theorem fixCard_sq_le_card {σ : F ≃+* F} (hσ : σ ≠ 1) : fixCard σ ^ 2 ≤ Nat.card F := by
  rw [card_eq_fixCard_pow σ]
  exact Nat.pow_le_pow_right (fixCard_pos σ) (two_le_orderOf hσ)

theorem fixCard_lt_card {σ : F ≃+* F} (hσ : σ ≠ 1) : fixCard σ < Nat.card F := by
  have h2 := two_le_fixCard σ
  have := fixCard_sq_le_card hσ
  nlinarith

end Order

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem card_Fq : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n H.n_ne_zero

include H in
theorem fixCard_pow_chi (m : ↥M) : fixCard (H.chi m) ^ orderOf (H.chi m) = 2 ^ n := by
  rw [← H.card_Fq, card_eq_fixCard_pow (H.chi m)]

theorem isCyclic_aut (n : ℕ) : IsCyclic (Fq n ≃+* Fq n) :=
  isCyclic_of_injective (MonoidHom.mk' (toGal n) (toGal_mul n)) (toGal_injective n)

include H in
theorem exists_mem_orderOf_chi_eq (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {B : Subgroup G}
    (hBT : B ≤ T) :
    ∃ (x : G) (hx : x ∈ B), orderOf (H.chi ⟨x, hT.le (hBT hx)⟩) =
      (Rl L T ⊔ Dc L T).relIndex B := by
  classical
  have : IsCyclic (Fq n ≃+* Fq n) := isCyclic_aut n
  let f : ↥B →* (Fq n ≃+* Fq n) :=
    H.chi.comp (Subgroup.inclusion (hBT.trans hT.le))
  have hker : f.ker = (Rl L T ⊔ Dc L T).subgroupOf B := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact H.chi_eq_one_iff_mem hT (hBT y.2)
  have h1 : (Rl L T ⊔ Dc L T).relIndex B = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥f.range)
  obtain ⟨b, hb⟩ := g.2
  refine ⟨b.1, b.2, ?_⟩
  have hgen : ∀ y : ↥f.range, y ∈ Subgroup.zpowers g := hg
  have h2 : orderOf g = Nat.card f.range := orderOf_eq_card_of_forall_mem_zpowers hgen
  have h3 : orderOf (H.chi ⟨b.1, hT.le (hBT b.2)⟩) = orderOf g := by
    rw [← Subgroup.orderOf_coe g, ← hb]
    rfl
  rw [h3, h2, h1]

end CoordData

namespace CoordData

variable {L M T : Subgroup G} {n : ℕ} (H : CoordData G L M n)

include H in
theorem fixCard_chi_of_not_mem (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G} (hx : x ∈ T)
    (hx1 : x ∉ Rl L T ⊔ Dc L T) :
    fixCard (H.chi ⟨x, hT.le hx⟩) ^ 2 ≤ 2 ^ n ∧ fixCard (H.chi ⟨x, hT.le hx⟩) < 2 ^ n := by
  have hσ : H.chi ⟨x, hT.le hx⟩ ≠ 1 := fun h => hx1 ((H.chi_eq_one_iff_mem hT hx).1 h)
  rw [← H.card_Fq]
  exact ⟨fixCard_sq_le_card hσ, fixCard_lt_card hσ⟩

include H in
theorem relIndex_Ec_le_cube (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T) {x : G}
    (hx : x ∈ T) {X : Subgroup G} (hXD : X ≤ Dc L T) (hxX : ∀ u ∈ X, x * u = u * x) :
    (Ec L T ⊓ X).relIndex X ≤ fixCard (H.chi ⟨x, hT.le hx⟩) ^ 3 := by
  have h1 := H.relIndex_sup_le hT hA hx hXD hxX
  have h2 := H.relIndex_Ec_le hT hx (Y := (blockU L ⊔ Ec L T) ⊓ X) inf_le_left
    (fun u hu => hxX u hu.2)
  have e : Ec L T ⊓ ((blockU L ⊔ Ec L T) ⊓ X) = Ec L T ⊓ X := by
    ext y
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, Subgroup.mem_sup_right h.1, h.2⟩⟩
  rw [e] at h2
  have hle : Ec L T ⊓ X ≤ (blockU L ⊔ Ec L T) ⊓ X := inf_le_inf_right _ le_sup_right
  have h3 := Subgroup.relIndex_mul_relIndex (Ec L T ⊓ X) ((blockU L ⊔ Ec L T) ⊓ X) X hle
    inf_le_right
  rw [← h3]
  calc (Ec L T ⊓ X).relIndex ((blockU L ⊔ Ec L T) ⊓ X) *
        ((blockU L ⊔ Ec L T) ⊓ X).relIndex X
      ≤ fixCard (H.chi ⟨x, hT.le hx⟩) ^ 2 * fixCard (H.chi ⟨x, hT.le hx⟩) :=
        Nat.mul_le_mul h2 h1
    _ = fixCard (H.chi ⟨x, hT.le hx⟩) ^ 3 := by ring

include H in
theorem card_blockU_inf_centralizer_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {x : G}
    (hx : x ∈ T) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      fixCard (H.chi ⟨x, hT.le hx⟩) ^ 2 * Nat.card ↥(blockZ L) := by
  set Y : Subgroup G := blockU L ⊓ Subgroup.centralizer ({x} : Set G) with hY
  have hYVE : Y ≤ blockU L ⊔ Ec L T := inf_le_left.trans le_sup_left
  have hxY : ∀ u ∈ Y, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.1 hu.2).symm
  have h1 := H.relIndex_Ec_le hT hx hYVE hxY
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Ec L T) (K := Y)
  have h3 : Nat.card ↥(Ec L T ⊓ Y) ≤ Nat.card ↥(blockZ L) := by
    refine Subgroup.card_le_of_le fun u hu => ⟨hu.2.1, ?_⟩
    exact hu.1.2
  rw [← h2]
  exact Nat.mul_le_mul h1 h3

include H in
theorem card_Rl_inf_centralizer_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hA : H.Adapted T)
    {x : G} (hx : x ∈ T) :
    Nat.card ↥(Rl L T ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      fixCard (H.chi ⟨x, hT.le hx⟩) * Nat.card ↥(oTwoIn L) := by
  set X : Subgroup G := Rl L T ⊓ Subgroup.centralizer ({x} : Set G) with hX
  have hXT₁ : X ≤ Rl L T ⊔ Dc L T := inf_le_left.trans le_sup_left
  have hxX : ∀ u ∈ X, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.1 hu.2).symm
  have h1 := H.relIndex_Dc_le hT hA hx hXT₁ hxX
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Dc L T) (K := X)
  have h3 : Nat.card ↥(Dc L T ⊓ X) ≤ Nat.card ↥(oTwoIn L) := by
    refine Subgroup.card_le_of_le fun u hu => ?_
    rw [← Rl_inf_Dc H.nat H.le H.normal hT]
    exact ⟨hu.2.1, hu.1⟩
  rw [← h2]
  exact Nat.mul_le_mul h1 h3

end CoordData

end CFSG.CGT.PushingUpLit.T2KSW
