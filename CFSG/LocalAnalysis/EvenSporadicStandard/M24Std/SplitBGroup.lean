module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBGen

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open Matrix Subgroup

variable {G : Type} [Group G] {U W : Subgroup G} {z : G} {ε : (Fin 4 → F2) → G}

@[expose] def phi (z w : G) : G := z * (w⁻¹ * z * w)

theorem phi_eq_one_iff (hz : z * z = 1) {w : G} : phi z w = 1 ↔ z * w = w * z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  unfold phi
  constructor
  · intro h
    have h1 : w⁻¹ * z * w = z := by
      have := eq_inv_of_mul_eq_one_right h
      rwa [hzi] at this
    calc z * w = w * (w⁻¹ * z * w) := by group
      _ = w * z := by rw [h1]
  · intro h
    calc z * (w⁻¹ * z * w) = z * (w⁻¹ * (z * w)) := by group
      _ = z * (w⁻¹ * (w * z)) := by rw [h]
      _ = z * z := by group
      _ = 1 := hz

theorem conj_z_eq (hz : z * z = 1) (w : G) : w⁻¹ * z * w = z * phi z w := by
  unfold phi
  calc w⁻¹ * z * w = (z * z) * (w⁻¹ * z * w) := by rw [hz, one_mul]
    _ = z * (z * (w⁻¹ * z * w)) := by group

theorem phi_mul (E : SplitHyp U W z ε) {w w' : G} (hw : w ∈ W) (hw' : w' ∈ W) :
    phi z (w * w') = phi z w * phi z w' := by
  have hu : phi z w ∈ U := E.phi_mem w hw
  have hu' : phi z w' ∈ U := E.phi_mem w' hw'
  have h1 : w⁻¹ * z * w = z * phi z w := conj_z_eq E.z_sq w
  have h2 : w'⁻¹ * phi z w * w' = phi z w := by
    have := E.central w'⁻¹ (inv_mem hw') _ hu
    calc w'⁻¹ * phi z w * w' = (w'⁻¹ * phi z w) * w' := by group
      _ = (phi z w * w'⁻¹) * w' := by rw [this]
      _ = phi z w := by group
  have h3 : phi z w * phi z w' = phi z w' * phi z w :=
    E.central _ (E.U_le hu) _ hu'
  calc phi z (w * w') = z * ((w * w')⁻¹ * z * (w * w')) := rfl
    _ = z * (w'⁻¹ * (w⁻¹ * z * w) * w') := by group
    _ = z * (w'⁻¹ * (z * phi z w) * w') := by rw [h1]
    _ = z * ((w'⁻¹ * z * w') * (w'⁻¹ * phi z w * w')) := by group
    _ = (z * (w'⁻¹ * z * w')) * phi z w := by rw [h2]; group
    _ = phi z w' * phi z w := rfl
    _ = phi z w * phi z w' := h3.symm

theorem phi_one (hz : z * z = 1) : phi z (1 : G) = 1 := by
  simp [phi, hz]

theorem mem_sup_zpowers (hz : z * z = 1) (hzU : ∀ u ∈ U, z * u = u * z) {x : G}
    (hx : x ∈ U ⊔ zpowers z) : x ∈ U ∨ z * x ∈ U := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let P : Subgroup G :=
    { carrier := {x | x ∈ U ∨ z * x ∈ U}
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · refine Or.inr ?_
          have e : z * (a * b) = a * (z * b) :=
            calc z * (a * b) = (z * a) * b := by group
              _ = (a * z) * b := by rw [hzU a ha]
              _ = a * (z * b) := by group
          rw [e]; exact mul_mem ha hb
        · refine Or.inr ?_
          have e : z * (a * b) = (z * a) * b := by group
          rw [e]; exact mul_mem ha hb
        · refine Or.inl ?_
          have h1 : z * (z * a) = (z * a) * z := hzU _ ha
          have h2 : a = z * a * z :=
            calc a = (z * z) * a := by rw [hz, one_mul]
              _ = z * (z * a) := by group
              _ = (z * a) * z := h1
          have e : a * b = (z * a) * (z * b) :=
            calc a * b = (z * a * z) * b := by rw [← h2]
              _ = (z * a) * (z * b) := by group
          rw [e]; exact mul_mem ha hb
      one_mem' := Or.inl U.one_mem
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          have hu : a⁻¹ * z ∈ U := by
            have := inv_mem ha
            rwa [mul_inv_rev, hzi] at this
          have h1 : z * (a⁻¹ * z) = (a⁻¹ * z) * z := hzU _ hu
          have h2 : z * a⁻¹ = a⁻¹ * z := by
            calc z * a⁻¹ = z * a⁻¹ * (z * z) := by rw [hz, mul_one]
              _ = (z * (a⁻¹ * z)) * z := by group
              _ = ((a⁻¹ * z) * z) * z := by rw [h1]
              _ = a⁻¹ * z := by
                calc ((a⁻¹ * z) * z) * z = a⁻¹ * (z * z) * z := by group
                  _ = a⁻¹ * z := by rw [hz]; group
          rw [h2]; exact hu }
  have hle : U ⊔ zpowers z ≤ P := sup_le (fun u hu => Or.inl hu) (by
    rw [zpowers_le]
    exact Or.inr (by rw [hz]; exact U.one_mem))
  exact hle hx

theorem phi_conj {h : G} (hh : z * h = h * z) (w : G) :
    phi z (h * w * h⁻¹) = h * phi z w * h⁻¹ := by
  have hzh : h⁻¹ * z * h = z := by
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hh]
      _ = z := by group
  unfold phi
  calc z * ((h * w * h⁻¹)⁻¹ * z * (h * w * h⁻¹))
      = z * (h * w⁻¹ * (h⁻¹ * z * h) * w * h⁻¹) := by group
    _ = z * (h * (w⁻¹ * z * w) * h⁻¹) := by rw [hzh]; group
    _ = (z * h) * (w⁻¹ * z * w) * h⁻¹ := by group
    _ = h * z * (w⁻¹ * z * w) * h⁻¹ := by rw [hh]
    _ = h * (z * (w⁻¹ * z * w)) * h⁻¹ := by group

@[expose] def conjHom (W : Subgroup G) (h : G) (hh : ∀ w ∈ W, h * w * h⁻¹ ∈ W) : ↥W →* ↥W where
  toFun w := ⟨h * w * h⁻¹, hh w w.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul]
    group

theorem exists_split (E : SplitHyp U W z ε) {H : Subgroup G} {m : ℕ} {g : Fin m → G}
    {A : Fin m → Mat4}
    (hHU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) (hHz : ∀ h ∈ H, z * h = h * z)
    (hgH : ∀ k, g k ∈ H)
    (hcent : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h ∈ U)
    (hgen : ∀ M N : Mat4, M * N = 1 → ∃ l : List (Fin m), wordMat A l = M)
    (hact : ∀ k c, g k * ε c * (g k)⁻¹ = ε (c ᵥ* A k))
    {ρ : Type*} [Fintype ρ] {words : ρ → List (Fin m)}
    (hrel : ∀ r, wordMat A (words r) = 1)
    {Psi : Fin m → Mat4} {Cm : Fin m → ρ → Mat4}
    (hdual : ∀ k k' : Fin m, (if k = k' then (1 : Mat4) else 0) =
      (1 + A k) * Psi k' + ∑ r, Cm k r * wordBlk A k' (words r)) :
    ∃ Y : Subgroup G, U ≤ Y ∧ Y ≤ W ∧ z ∉ Y ∧ (∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) ∧
      ∀ w ∈ W, w ∈ Y ∨ z * w ∈ Y := by
  classical
  have hε0 : ε 0 = 1 := eps_zero E
  obtain ⟨cd, hcd_eps, hcd_mem, hcd_mul, hcd_one⟩ := exists_coords E
  let Φ : ↥W →* Multiplicative (Fin 4 → F2) :=
    { toFun := fun w => Multiplicative.ofAdd (cd (phi z w))
      map_one' := by
        show Multiplicative.ofAdd (cd (phi z ((1 : ↥W) : G))) = 1
        rw [Subgroup.coe_one, phi_one E.z_sq, hcd_one]; rfl
      map_mul' := by
        intro w w'
        show Multiplicative.ofAdd (cd (phi z ((w * w' : ↥W) : G))) = _
        rw [Subgroup.coe_mul, phi_mul E w.2 w'.2,
          hcd_mul (phi z w) (E.phi_mem _ w.2) (phi z w') (E.phi_mem _ w'.2)]
        rfl }
  have hΦ : ∀ w : ↥W, Φ w = Multiplicative.ofAdd (cd (phi z w)) := fun w => rfl
  have hN : (U.subgroupOf W).Normal := by
    refine ⟨fun n hn w => ?_⟩
    have hn' : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
    have : w * n * w⁻¹ = n := by
      apply Subtype.ext
      have := E.central w w.2 n hn'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (w : G) * n * (w : G)⁻¹ = (n * w) * (w : G)⁻¹ := by rw [this]
        _ = n := by group
    rw [this]; exact hn
  have hq2 : ∀ q : ↥W ⧸ U.subgroupOf W, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact E.sq_mem w w.2
  have hqc : ∀ q q' : ↥W ⧸ U.subgroupOf W, q * q' = q' * q := by
    intro q q'
    have hinv : ∀ q : ↥W ⧸ U.subgroupOf W, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (hq2 q)
    calc q * q' = (q * q')⁻¹ := (hinv _).symm
      _ = q'⁻¹ * q⁻¹ := mul_inv_rev _ _
      _ = q' * q := by rw [hinv, hinv]
  let _hCG : CommGroup (↥W ⧸ U.subgroupOf W) :=
    { (inferInstance : Group (↥W ⧸ U.subgroupOf W)) with mul_comm := hqc }
  have hV2 : ∀ x : Additive (↥W ⧸ U.subgroupOf W), x + x = 0 := by
    intro x
    exact congrArg Additive.ofMul (hq2 x.toMul)
  let _hMod : Module F2 (Additive (↥W ⧸ U.subgroupOf W)) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by rw [two_nsmul]; exact hV2 x)
  let π : ↥W → Additive (↥W ⧸ U.subgroupOf W) := fun w => Additive.ofMul (QuotientGroup.mk w)
  have hπ_mul : ∀ w w' : ↥W, π (w * w') = π w + π w' := fun w w' => rfl
  have hπ_surj : ∀ v : Additive (↥W ⧸ U.subgroupOf W), ∃ w : ↥W, π w = v := by
    intro v
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective v.toMul
    exact ⟨w, by simp [π, hw]⟩
  have hπ_zero : ∀ w : ↥W, π w = 0 ↔ (w : G) ∈ U := by
    intro w
    show Additive.ofMul (QuotientGroup.mk w) = 0 ↔ _
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hΦN : U.subgroupOf W ≤ Φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    have hn' : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
    rw [hΦ, (phi_eq_one_iff E.z_sq).2 (E.z_comm_U _ hn'), hcd_one]
    rfl
  let pb : Additive (↥W ⧸ U.subgroupOf W) →ₗ[F2] (Fin 4 → F2) :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditiveLeft (QuotientGroup.lift _ Φ hΦN))
  have hpb : ∀ w : ↥W, pb (π w) = cd (phi z w) := fun w => rfl
  have hconj_le : ∀ h : ↥H,
      U.subgroupOf W ≤ (U.subgroupOf W).comap (conjHom W h (hHW h h.2)) := by
    intro h n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    show (h : G) * (n : G) * (h : G)⁻¹ ∈ U
    exact hHU h h.2 n (Subgroup.mem_subgroupOf.1 hn)
  let Tfun : ↥H → Additive (↥W ⧸ U.subgroupOf W) →ₗ[F2] Additive (↥W ⧸ U.subgroupOf W) :=
    fun h => AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive
      (QuotientGroup.map (U.subgroupOf W) (U.subgroupOf W) (conjHom W h (hHW h h.2))
        (hconj_le h)))
  have hT_apply : ∀ (h : ↥H) (w : ↥W),
      Tfun h (π w) = π (conjHom W h (hHW h h.2) w) := fun h w => rfl
  have hT_mul : ∀ h h' : ↥H, Tfun (h * h') = Tfun h * Tfun h' := by
    intro h h'
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := hπ_surj v
    rw [Module.End.mul_apply, hT_apply, hT_apply, hT_apply]
    congr 1
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
    group
  have hT_one : Tfun 1 = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := hπ_surj v
    rw [hT_apply, Module.End.one_apply]
    congr 1
    apply Subtype.ext
    simp [conjHom]
  have hT_U : ∀ (u : G) (hu : u ∈ U) (hh : u ∈ H), Tfun ⟨u, hh⟩ = 1 := by
    intro u hu hh
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := hπ_surj v
    rw [hT_apply, Module.End.one_apply]
    congr 1
    apply Subtype.ext
    show u * (w : G) * u⁻¹ = w
    have := E.central w w.2 u hu
    calc u * (w : G) * u⁻¹ = (w * u) * u⁻¹ := by rw [this]
      _ = w := by group
  choose yw hywW hyw using fun i : Fin 4 => E.phi_surj (ε (Pi.single i 1)) (E.eps_mem _)
  have hpy : ∀ i, pb (π ⟨yw i, hywW i⟩) = Pi.single i 1 := by
    intro i
    rw [hpb]
    show cd (phi z (yw i)) = _
    rw [show phi z (yw i) = ε (Pi.single i 1) from hyw i, hcd_eps]
  have hpz : pb (π ⟨z, E.z_mem⟩) = 0 := by
    rw [hpb]
    show cd (phi z z) = 0
    rw [show phi z z = 1 by simp [phi, E.z_sq], hcd_one]
  have hker : ∀ v, pb v = 0 → ∃ a : F2, v = a • π ⟨z, E.z_mem⟩ := by
    intro v hv
    obtain ⟨w, rfl⟩ := hπ_surj v
    rw [hpb] at hv
    have h1 : phi z w = 1 := by
      have h2 : phi z w ∈ U := E.phi_mem w w.2
      rw [← hcd_mem _ h2, hv, hε0]
    have h3 : z * (w : G) = w * z := (phi_eq_one_iff E.z_sq).1 h1
    rcases mem_sup_zpowers E.z_sq E.z_comm_U (E.ker_phi w w.2 h3) with h | h
    · exact ⟨0, by rw [(hπ_zero w).2 h, zero_smul]⟩
    · refine ⟨1, ?_⟩
      rw [one_smul]
      have h4 : π (⟨z, E.z_mem⟩ * w) = 0 := (hπ_zero _).2 h
      rw [hπ_mul] at h4
      calc π w = π ⟨z, E.z_mem⟩ + π ⟨z, E.z_mem⟩ + π w := by rw [hV2, zero_add]
        _ = π ⟨z, E.z_mem⟩ + (π ⟨z, E.z_mem⟩ + π w) := by rw [add_assoc]
        _ = π ⟨z, E.z_mem⟩ := by rw [h4, add_zero]
  have hz : π ⟨z, E.z_mem⟩ ≠ 0 := fun h => E.z_not_mem ((hπ_zero _).1 h)
  have hTz : ∀ k, Tfun ⟨g k, hgH k⟩ (π ⟨z, E.z_mem⟩) = π ⟨z, E.z_mem⟩ := by
    intro k
    rw [hT_apply]
    congr 1
    apply Subtype.ext
    show g k * z * (g k)⁻¹ = z
    rw [← hHz _ (hgH k)]
    group
  have hTp : ∀ k v, pb (Tfun ⟨g k, hgH k⟩ v) = pb v ᵥ* A k := by
    intro k v
    obtain ⟨w, rfl⟩ := hπ_surj v
    rw [hT_apply, hpb, hpb]
    show cd (phi z (g k * w * (g k)⁻¹)) = _
    rw [phi_conj (hHz _ (hgH k)) w]
    have hu : phi z w ∈ U := E.phi_mem w w.2
    conv_lhs => rw [← hcd_mem _ hu]
    rw [hact, hcd_eps]
  have hTword : ∀ l : List (Fin m), (l.map (fun k => Tfun ⟨g k, hgH k⟩)).prod =
      Tfun ⟨(l.map g).prod, prod_map_mem hgH l⟩ := by
    intro l
    induction l with
    | nil => exact hT_one.symm
    | cons k l ih =>
      rw [List.map_cons, List.prod_cons, ih]
      exact (hT_mul ⟨g k, hgH k⟩ ⟨(l.map g).prod, prod_map_mem hgH l⟩).symm
  have hwords : ∀ r, ((words r).map (fun k => Tfun ⟨g k, hgH k⟩)).prod = 1 := by
    intro r
    rw [hTword]
    exact hT_U _ (prod_mem_U E hgH hcent hact (hrel r)) _
  obtain ⟨f, hfz, hfT⟩ := exists_invariant_functional (V := Additive (↥W ⧸ U.subgroupOf W))
    (fun i => π ⟨yw i, hywW i⟩) (π ⟨z, E.z_mem⟩) pb hpy hpz hker hz
    (fun k => Tfun ⟨g k, hgH k⟩) A hTz hTp words hwords Psi Cm hdual
  have hfword : ∀ (l : List (Fin m)) v,
      f ((l.map (fun k => Tfun ⟨g k, hgH k⟩)).prod v) = f v := by
    intro l
    induction l with
    | nil => intro v; simp
    | cons k l ih =>
      intro v
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, hfT, ih]
  have hfH : ∀ h (hh : h ∈ H) v, f (Tfun ⟨h, hh⟩ v) = f v := by
    intro h hh v
    obtain ⟨l, hl⟩ := exists_word_mul E hHU hgH hcent hgen hact hh
    have hu : (l.map g).prod⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (prod_map_mem hgH l)) hh
    have hsplit : (⟨h, hh⟩ : ↥H) =
        ⟨(l.map g).prod, prod_map_mem hgH l⟩ * ⟨(l.map g).prod⁻¹ * h, hu⟩ :=
      Subtype.ext (by simp)
    rw [hsplit, hT_mul, Module.End.mul_apply, hT_U _ hl hu, Module.End.one_apply, ← hTword l,
      hfword]
  let fW : ↥W →* Multiplicative F2 :=
    (AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom).comp
      (QuotientGroup.mk' (U.subgroupOf W))
  have hfW : ∀ w : ↥W, fW w = Multiplicative.ofAdd (f (π w)) := fun w => rfl
  have hker_iff : ∀ w : ↥W, w ∈ fW.ker ↔ f (π w) = 0 := by
    intro w
    rw [MonoidHom.mem_ker, hfW]
    exact Iff.rfl
  refine ⟨(fW.ker).map W.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    refine ⟨⟨u, E.U_le hu⟩, (hker_iff _).2 ?_, rfl⟩
    rw [(hπ_zero ⟨u, E.U_le hu⟩).2 hu, map_zero]
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = ⟨z, E.z_mem⟩ := Subtype.ext hwz
    have h0 := (hker_iff w).1 hw
    rw [hwz', hfz] at h0
    exact one_ne_zero h0
  · rintro h hh _ ⟨w, hw, rfl⟩
    refine ⟨⟨h * w * h⁻¹, hHW h hh w w.2⟩, (hker_iff _).2 ?_, rfl⟩
    have h0 := (hker_iff w).1 hw
    have := hfH h hh (π w)
    rw [hT_apply] at this
    exact this.trans h0
  · intro w hw
    rcases F2_cases (f (π ⟨w, hw⟩)) with h0 | h1
    · exact Or.inl ⟨⟨w, hw⟩, (hker_iff _).2 h0, rfl⟩
    · refine Or.inr ⟨⟨z * w, mul_mem E.z_mem hw⟩, (hker_iff _).2 ?_, rfl⟩
      rw [show (⟨z * w, mul_mem E.z_mem hw⟩ : ↥W) = ⟨z, E.z_mem⟩ * ⟨w, hw⟩ from rfl, hπ_mul,
        map_add, hfz, h1]
      exact F2_add_self 1

end CFSG.EvenSporadicStandard.M24Std.SplitB
