module

public import CFSG.CGT.Stroth77.Section47Strong
public import CFSG.CGT.Stroth77.Section43Sc
public import CFSG.CGT.Stroth77.Section47Fus
public import CFSG.CGT.Stroth77.Section47Core

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

@[expose] def H47SylowControl : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G) →
      ∃ k ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
        ∀ q ∈ Q, k⁻¹ * q * k ∈ (F.S : Subgroup G)

@[expose] def H47WeakClosure : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ k : G,
      (∀ d ∈ D, k⁻¹ * d * k ∈ (F.S : Subgroup G) ⊓
        Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G)) →
      D.map (MulAut.conj k⁻¹).toMonoidHom = D

@[expose] def H47ConjInD : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g ∈ D →
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g = (dD.c : G) ^ 2 ^ (m - 2) ∨
        g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹



@[expose] def H47H9 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ X : Subgroup G, X ≤ (F.S : Subgroup G) ⊓
      Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G) →
      IsMulCommutative X → Nat.card X = Nat.card D → X = D

theorem H47WeakClosure_of_h9 (h9 : H47H9) : H47WeakClosure := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel k hk
  haveI := dD.isMulCommutative
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hDz : D ≤ Subgroup.centralizer ({z} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mul_comm_of_mem_isMulCommutative D hd (D.pow_mem dD.c.2 _))
  refine h9 F hm dD h hSN hnc e he hS hrel _ ?_ ?_ (Subgroup.card_map_of_injective
    (MulAut.conj k⁻¹).injective)
  · rintro _ ⟨d, hd, rfl⟩
    simpa using hk d hd
  · haveI := dD.isMulCommutative
    exact Subgroup.map_isMulCommutative D _

theorem H47SylowControl_of_h9 (h9 : H47H9) : H47SylowControl := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel Q hQ hQz
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := dD.isMulCommutative
  set P := Subgroup.closure {dD.uv, dD.t, dD.u} with hP
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  have hPS : P ≤ (F.S : Subgroup G) := by rw [hS]; exact le_sup_right.trans le_sup_left
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have h3 := dD.t200_h3 (by omega : 1 ≤ m)
  have hncA : ∃ x ∈ omegaIn 1 F.A, ∃ y ∈ omegaIn 1 F.A,
      orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y := by
    obtain ⟨x, hx, hox, y, hy, hoy, hxy⟩ := hnc
    rw [h.omegaIn_one_eq] at hx hy
    exact ⟨x, hx, y, hy, hox, hoy, hxy⟩
  have hza := h.not_isConj_of_omega hncA h3
  have h3' : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z →
      ∃ p ∈ P, p⁻¹ * y * p = z := by
    intro y hyD hy2 hy1 hyz
    rcases h3 y hyD hy2 hy1 with hp | ⟨g, -, hg⟩
    · exact hp
    · exact absurd (hyz.symm.trans (Stroth42.isConj_of_conj_eq hg).symm) hza
  have hz2 : z * z = 1 := by rw [hz]; exact Stroth47Fus.t200_c₁_mul_self dD (by omega)
  have hz1 : z ≠ 1 := by rw [hz]; exact Stroth47Fus.t200_c₁_ne_one dD (by omega)
  exact Stroth42.exists_conj_le_centralizer F.S dD.isMulCommutative h.le_S hSN hPS hzD h3'
    hz2 hz1 (fun X hX hab hcard => h9 F hm dD h hSN hnc e he hS hrel X hX hab hcard) hQ hQz



theorem H47_exists_normalizer_conj_eq (hSylow : H47SylowControl) (hWeak : H47WeakClosure)
    {F : StrothFrame G} {D : Subgroup G} {m : ℕ} {dD : StrothWeakTypeData D (.t200 m)}
    (h : F.IsD D dD) (hm : 2 ≤ m)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hnc : ∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y)
    {e : G} (he : e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e)
    (hrel : Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)
    {g y : G} (hg : g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G))
    (hyD : y ∈ D) (hgy : g⁻¹ * y * g ∈ D) :
    ∃ n ∈ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      n⁻¹ * y * n = g⁻¹ * y * g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := dD.isMulCommutative
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set y' := g⁻¹ * y * g with hy'
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set H := Z ⊓ Subgroup.centralizer {y'} with hH
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDz : D ≤ Z := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hDH : D ≤ H := le_inf hDz (fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd y' hgy))
  have hDp : IsPGroup 2 D := F.S.isPGroup'.to_le h.le_S
  obtain ⟨P, hP, hDP⟩ := Stroth43Sc.exists_isSylowOf_le hDH hDp
  set Q₀ := D.map (MulAut.conj g⁻¹).toMonoidHom with hQ₀
  have hQ₀H : Q₀ ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcommD d hd y hyD
    calc g⁻¹ * d * g * (g⁻¹ * y * g) = g⁻¹ * (d * y) * g := by group
      _ = g⁻¹ * (y * d) * g := by rw [this]
      _ = g⁻¹ * y * g * (g⁻¹ * d * g) := by group
  obtain ⟨c, hcH, hcQ⟩ := Stroth43Sc.exists_conj_le_of_isSylowOf hP hQ₀H (hDp.map _)
  have hcz : c ∈ Z := (Subgroup.mem_inf.1 hcH).1
  obtain ⟨k, hkz, hkP⟩ := hSylow F hm dD h hSN hnc e he hS hrel P hP.isPGroup
    (hP.le.trans inf_le_left)
  have hk : D.map (MulAut.conj k⁻¹).toMonoidHom = D :=
    hWeak F hm dD h hSN hnc e he hS hrel k (fun d hd => Subgroup.mem_inf.2
      ⟨hkP d (hDP hd), Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (hDz hd)) hkz⟩)
  have hgck : D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom = D := by
    refine hWeak F hm dD h hSN hnc e he hS hrel (g * c * k) (fun d hd => ?_)
    have hq : g⁻¹ * d * g ∈ Q₀ := ⟨d, hd, by simp⟩
    rw [show (g * c * k)⁻¹ * d * (g * c * k) = k⁻¹ * (c⁻¹ * (g⁻¹ * d * g) * c) * k by group]
    refine Subgroup.mem_inf.2 ⟨hkP _ (hcQ _ hq), ?_⟩
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (Z.mul_mem (Z.mul_mem (Z.inv_mem hcz)
      (Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg)) hcz)) hkz
  refine ⟨g * c, Subgroup.mem_inf.2 ⟨?_, Z.mul_mem hg hcz⟩, ?_⟩
  · apply Stroth43Sc.mem_normalizer_of_conj_mem
    intro d hd
    have h1 : (g * c * k)⁻¹ * d * (g * c * k) ∈ D :=
      (Stroth43Sc.conj_mem_iff_of_map_eq hgck).mpr hd
    rw [show (g * c * k)⁻¹ * d * (g * c * k) =
      k⁻¹ * ((g * c)⁻¹ * d * (g * c)) * k by group] at h1
    exact (Stroth43Sc.conj_mem_iff_of_map_eq hk).mp h1
  · have hcy := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcH).2
    calc (g * c)⁻¹ * y * (g * c) = c⁻¹ * (y' * c) := by rw [hy']; group
      _ = c⁻¹ * (c * y') := by rw [hcy]
      _ = g⁻¹ * y * g := by rw [hy']; group

@[expose] def H47Normalizer : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ n ∈ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      n⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * n = (dD.c : G) ^ 2 ^ (m - 2) ∨
        n⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * n = ((dD.c : G) ^ 2 ^ (m - 2))⁻¹

theorem H47ConjInD_of_normalizer (hNorm : H47Normalizer)
    (hSylow : H47SylowControl) (hWeak : H47WeakClosure) : H47ConjInD := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel g hg hgD
  obtain ⟨n, hn, hng⟩ := H47_exists_normalizer_conj_eq hSylow hWeak h hm hSN hnc he hS hrel
    hg (D.pow_mem dD.c.2 _) hgD
  rw [← hng]
  exact hNorm F hm dD h hSN hnc e he hS hrel n hn

theorem H47Extremal_of_inputs (hSylow : H47SylowControl) (hWeak : H47WeakClosure)
    (hConjD : H47ConjInD) :
    ∀ {G : Type} [Group G] [Finite G] (F : StrothFrame G) {D : Subgroup G} {m : ℕ},
    2 ≤ m → ∀ (dD : StrothWeakTypeData D (.t200 m)), F.IsD D dD →
    (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G) →
    (∃ x ∈ omegaIn 1 D, orderOf x = 2 ∧ ∃ y ∈ omegaIn 1 D, orderOf y = 2 ∧
      ¬ IsConj x y) →
    ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
    (F.S : Subgroup G) = D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e →
    (Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
      Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3) →
    ∀ g ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
      g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g ∈ H47C_S F dD →
      ∃ k ∈ Subgroup.centralizer ({(dD.c : G) ^ 2 ^ (m - 1)} : Set G),
        (k⁻¹ * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * k =
            (dD.c : G) ^ 2 ^ (m - 2) ∨
          k⁻¹ * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * k =
            ((dD.c : G) ^ 2 ^ (m - 2))⁻¹) ∧
        ∀ s ∈ H47C_S F dD,
          s * (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) =
            (g⁻¹ * ((dD.c : G) ^ 2 ^ (m - 2)) * g) * s →
          k⁻¹ * s * k ∈ (F.S : Subgroup G) := by
  intro G _ _ F D m hm dD h hSN hnc e he hS hrel g hg hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := (dD.c : G) ^ 2 ^ (m - 1) with hz
  set c₂ := (dD.c : G) ^ 2 ^ (m - 2) with hc₂
  set Z := Subgroup.centralizer ({z} : Set G) with hZ
  set y := g⁻¹ * c₂ * g with hydef
  set H := Z ⊓ Subgroup.centralizer {y} with hH
  set Ty := (F.S : Subgroup G) ⊓ Z ⊓ Subgroup.centralizer {y} with hTy
  have hzD : z ∈ D := D.pow_mem dD.c.2 _
  have hc₂D : c₂ ∈ D := D.pow_mem dD.c.2 _
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hDz : D ≤ Z := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommD d hd z hzD)
  have hyZ : y ∈ Z := Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hc₂D)) hg
  have hTyH : Ty ≤ H := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2,
      (Subgroup.mem_inf.1 hx).2⟩
  have hTyp : IsPGroup 2 Ty := F.S.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨R, hR, hTyR⟩ := Stroth43Sc.exists_isSylowOf_le hTyH hTyp
  set Q₀ := D.map (MulAut.conj g⁻¹).toMonoidHom with hQ₀
  have hQ₀H : Q₀ ≤ H := by
    rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hcommD d hd c₂ hc₂D
    calc g⁻¹ * d * g * (g⁻¹ * c₂ * g) = g⁻¹ * (d * c₂) * g := by group
      _ = g⁻¹ * (c₂ * d) * g := by rw [this]
      _ = g⁻¹ * c₂ * g * (g⁻¹ * d * g) := by group
  have hDp : IsPGroup 2 D := F.S.isPGroup'.to_le h.le_S
  obtain ⟨c, hcH, hcQ⟩ := Stroth43Sc.exists_conj_le_of_isSylowOf hR hQ₀H (hDp.map _)
  have hcz : c ∈ Z := (Subgroup.mem_inf.1 hcH).1
  obtain ⟨k, hkz, hkR⟩ := hSylow F hm dD h hSN hnc e he hS hrel R hR.isPGroup
    (hR.le.trans inf_le_left)
  have hgck : D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom = D := by
    refine hWeak F hm dD h hSN hnc e he hS hrel (g * c * k) (fun d hd => ?_)
    have hq : g⁻¹ * d * g ∈ Q₀ := ⟨d, hd, by simp⟩
    rw [show (g * c * k)⁻¹ * d * (g * c * k) =
      k⁻¹ * (c⁻¹ * (g⁻¹ * d * g) * c) * k by group]
    refine Subgroup.mem_inf.2 ⟨hkR _ (hcQ _ hq), ?_⟩
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem hkz) (Z.mul_mem (Z.mul_mem (Z.inv_mem hcz)
      (Z.mul_mem (Z.mul_mem (Z.inv_mem hg) (hDz hd)) hg)) hcz)) hkz
  have hyS : y ∈ (F.S : Subgroup G) := (Subgroup.mem_inf.mp hy).1
  have hyZ' : y ∈ Z := (Subgroup.mem_inf.mp hy).2
  have hyR : y ∈ R := hTyR (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyS, hyZ'⟩,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
  have hykD : k⁻¹ * y * k ∈ D := by
    rw [← h.cent]
    refine Subgroup.mem_inf.2 ⟨hkR y hyR, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ D.map (MulAut.conj (g * c * k)⁻¹).toMonoidHom := hgck.symm ▸ hd
    obtain ⟨d', hd'D, rfl⟩ := hd'
    have hq : c⁻¹ * (g⁻¹ * d' * g) * c ∈ R := hcQ _ ⟨d', hd'D, by simp⟩
    have hqy : c⁻¹ * (g⁻¹ * d' * g) * c * y = y * (c⁻¹ * (g⁻¹ * d' * g) * c) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hR.le hq)).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc (g * c * k)⁻¹ * d' * (g * c * k) * (k⁻¹ * y * k) =
        k⁻¹ * (c⁻¹ * (g⁻¹ * d' * g) * c * y) * k := by group
      _ = k⁻¹ * (y * (c⁻¹ * (g⁻¹ * d' * g) * c)) * k := by rw [hqy]
      _ = k⁻¹ * y * k * ((g * c * k)⁻¹ * d' * (g * c * k)) := by group
  refine ⟨k, hkz, ?_, ?_⟩
  · have hgk : (g * k)⁻¹ * c₂ * (g * k) = k⁻¹ * y * k := by rw [hydef]; group
    have := hConjD F hm dD h hSN hnc e he hS hrel (g * k) (Z.mul_mem hg hkz) (by rw [hgk]; exact hykD)
    rw [hgk] at this
    exact this
  · intro s hsT hsy
    exact hkR s (hTyR (Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.mp hsT).1,
        (Subgroup.mem_inf.mp hsT).2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 hsy⟩))

theorem H47Extremal_of_inputs' (hSylow : H47SylowControl) (hWeak : H47WeakClosure)
    (hConjD : H47ConjInD) : H47Extremal :=
  H47Extremal_of_inputs hSylow hWeak hConjD

theorem H47Extremal_of_h9_normalizer (h9 : H47H9) (hNorm : H47Normalizer) : H47Extremal :=
  H47Extremal_of_inputs' (H47SylowControl_of_h9 h9) (H47WeakClosure_of_h9 h9)
    (H47ConjInD_of_normalizer hNorm (H47SylowControl_of_h9 h9) (H47WeakClosure_of_h9 h9))

end CFSG.CGT.Stroth77
