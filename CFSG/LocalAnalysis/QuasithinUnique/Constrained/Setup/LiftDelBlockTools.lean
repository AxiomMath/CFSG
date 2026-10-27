module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatY

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem oddOrderSubgroup_idem (H : Subgroup G) :
    oddOrderSubgroup (oddOrderSubgroup H) = oddOrderSubgroup H := by
  refine le_antisymm (oddOrderSubgroup_le _) ?_
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem pow_mem_of_mul_two_elt {Y N : Subgroup G} (hN : (N.subgroupOf Y).Normal) {x d z : G}
    (hx : x ∈ Y) (hz : z ∈ Y) (hd : d ∈ N) (hxdz : x = d * z) {k : ℕ} (hzk : z ^ k = 1) :
    x ^ k ∈ N := by
  have hdY : d ∈ Y := by
    have : d = x * z⁻¹ := by rw [hxdz]; group
    rw [this]
    exact Y.mul_mem hx (Y.inv_mem hz)
  have h1 : (QuotientGroup.mk (⟨d, hdY⟩ : Y) : Y ⧸ N.subgroupOf Y) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hd)
  have hmul : (⟨x, hx⟩ : Y) = ⟨d, hdY⟩ * ⟨z, hz⟩ := Subtype.ext hxdz
  have hz1 : (⟨z, hz⟩ : Y) ^ k = 1 := Subtype.ext (by simpa using hzk)
  have h2 : (QuotientGroup.mk (⟨x, hx⟩ : Y) : Y ⧸ N.subgroupOf Y) ^ k = 1 := by
    rw [hmul, QuotientGroup.mk_mul, h1, one_mul, ← QuotientGroup.mk_pow, hz1]
    rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.1 h2

theorem eq_of_map_le_of_two_kernel {A : Type} [Group A] (f : G →* A) {LS B D : Subgroup G}
    (hB : B ≤ LS) (hDB : D ≤ B) (hDn : (D.subgroupOf B).Normal)
    (hodd : oddOrderSubgroup B = B)
    (hker : ∀ x ∈ LS, f x = 1 → ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (himg : B.map f ≤ D.map f) : D = B := by
  refine le_antisymm hDB ?_
  rw [← hodd]
  refine oddOrderSubgroup_le_of_pow_mem fun x hx => ?_
  obtain ⟨d, hd, hdx⟩ := himg (Subgroup.mem_map_of_mem f hx)
  have hz : d⁻¹ * x ∈ B := B.mul_mem (B.inv_mem (hDB hd)) hx
  have hf : f (d⁻¹ * x) = 1 := by rw [map_mul, map_inv, hdx, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hker _ (hB hz) hf
  exact ⟨k, pow_mem_of_mul_two_elt hDn hx hz hd (by group) hk⟩

theorem commutator_le_of_le_normalizer {A C : Subgroup G}
    (h : C ≤ Subgroup.normalizer (A : Set G)) : ⁅A, C⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  have h1 : c * a⁻¹ * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (h hc) a⁻¹).1 (A.inv_mem ha)
  have : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact A.mul_mem ha h1

theorem le_normalizer_commutator (A C : Subgroup G) :
    A ⊔ C ≤ Subgroup.normalizer ((⁅A, C⁆ : Subgroup G) : Set G) := by
  have h : (⁅A, C⁆.subgroupOf (A ⊔ C)).Normal := inferInstance
  have hle : ⁅A, C⁆ ≤ A ⊔ C := by
    rw [Subgroup.commutator_le]
    intro a ha c hc
    have ha' : a ∈ A ⊔ C := Subgroup.mem_sup_left ha
    have hc' : c ∈ A ⊔ C := Subgroup.mem_sup_right hc
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' hc')
      (Subgroup.inv_mem _ ha')) (Subgroup.inv_mem _ hc')
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 h

theorem normal_commutator_subgroupOf {A C : Subgroup G}
    (h : C ≤ Subgroup.normalizer (A : Set G)) : (⁅A, C⁆.subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (commutator_le_of_le_normalizer h)]
  exact le_sup_left.trans (le_normalizer_commutator A C)

theorem commutator_le_of_le_of_le {A B K : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) : ⁅A, B⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA ha) (hB hc))
    (Subgroup.inv_mem _ (hA ha))) (Subgroup.inv_mem _ (hB hc))

theorem perfect_commutator_le_mod {K P X N : Subgroup G} (hPK : P ≤ K) (hXK : X ≤ K)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) (hP : ⁅P, P⁆ = P)
    (h : ⁅⁅P, X⁆, P⁆ ≤ N) : ⁅P, X⁆ ≤ N := by
  have hN' : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hK
  set P' : Subgroup ↥K := P.subgroupOf K with hP'
  set X' : Subgroup ↥K := X.subgroupOf K with hX'
  set N' : Subgroup ↥K := N.subgroupOf K with hN'def
  have hmapP : P'.map K.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPK
  have hmapX : X'.map K.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXK
  have hPP : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective (K.subtype_injective)
    rw [Subgroup.map_commutator, hmapP, hP]
  have hPXK : ⁅P, X⁆ ≤ K := commutator_le_of_le_of_le hPK hXK
  have h1 : ⁅⁅P', X'⁆, P'⁆ ≤ N' := by
    intro x hx
    have hx' : (x : G) ∈ (⁅⁅P', X'⁆, P'⁆).map K.subtype := Subgroup.mem_map_of_mem K.subtype hx
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapP, hmapX] at hx'
    exact Subgroup.mem_subgroupOf.2 (h hx')
  let π : ↥K →* ↥K ⧸ N' := QuotientGroup.mk' N'
  have hperf : Group.IsPerfect (P'.map π) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hPP]
  have h2 : ⁅⁅P'.map π, X'.map π⁆, P'.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact h1
  have h3 := CFSG.LocalCores.perfect_double_commutator hperf h2
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h3
  intro y hy
  have hyK : y ∈ K := hPXK hy
  have hy' : (⟨y, hyK⟩ : ↥K) ∈ ⁅P', X'⁆ := by
    have : y ∈ (⁅P', X'⁆).map K.subtype := by
      rw [Subgroup.map_commutator, hmapP, hmapX]
      exact hy
    obtain ⟨z, hz, hzy⟩ := this
    have hzz : z = ⟨y, hyK⟩ := Subtype.ext hzy
    rwa [hzz] at hz
  exact Subgroup.mem_subgroupOf.1 (h3 hy')

end General

section Rho

variable {G : Type} [Group G] {V : Subgroup G}

theorem modComm_le (V : Subgroup G) (A : Subgroup (MulAut V)) : modComm V A ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨a, -, v, rfl⟩
  exact V.mul_mem (a v).2 (V.inv_mem v.2)

theorem conj_mem_modComm [V.Normal] {A : Subgroup (MulAut V)} {g : G}
    (hg : MulAut.conjNormal (H := V) g ∈ Subgroup.normalizer (A : Set (MulAut V))) {u : G}
    (hu : u ∈ modComm V A) : g * u * g⁻¹ ∈ modComm V A := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, rfl⟩ := hx
    set φ : MulAut V := MulAut.conjNormal (H := V) g with hφ
    have ha' : φ * a * φ⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg a).1 ha
    have h1 : g * (((a v : V) : G) * (v : G)⁻¹) * g⁻¹ =
        (((φ * a * φ⁻¹) (φ v) : V) : G) * ((φ v : V) : G)⁻¹ := by
      have e1 : (((φ * a * φ⁻¹) (φ v) : V) : G) = ((φ (a v) : V) : G) := by
        simp [MulAut.mul_apply]
      rw [e1, hφ, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
      group
    rw [h1]
    exact Subgroup.subset_closure ⟨φ * a * φ⁻¹, ha', φ v, rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem le_normalizer_modComm [V.Normal] {A : Subgroup (MulAut V)} {K : Subgroup G}
    (h : autOn K V ≤ Subgroup.normalizer (A : Set (MulAut V))) :
    K ≤ Subgroup.normalizer ((modComm V A : Subgroup G) : Set G) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rintro _ ⟨x, hx, rfl⟩
  have hρ : MulAut.conjNormal (H := V) g ∈ autOn K V := by
    rw [autOn_eq_map_conjNormal]
    exact Subgroup.mem_map_of_mem _ hg
  exact conj_mem_modComm (h hρ) hx

theorem conjNormal_eq_one_iff [V.Normal] {x : G} :
    MulAut.conjNormal (H := V) x = 1 ↔ x ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h2 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc v * x = (x * v * x⁻¹) * x := by rw [h2]
      _ = x * v := by group
  · intro hc
    ext v
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have h := Subgroup.mem_centralizer_iff.mp hc v v.2
    show x * v * x⁻¹ = v
    rw [← h, mul_inv_cancel_right]

theorem two_elt_of_conjNormal_eq_one [Finite G] [V.Normal] {LS : Subgroup G}
    (hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS) {x : G} (hx : x ∈ LS)
    (h1 : MulAut.conjNormal (H := V) x = 1) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : x ∈ pCoreOf 2 LS := hker ▸ ⟨hx, conjNormal_eq_one_iff.1 h1⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LS ⟨x, hmem⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem rhoPreimage_top_eq_comap [V.Normal] (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (N : Subgroup (MulAut V)) :
    rhoPreimage V ⊤ hX N = N.comap (MulAut.conjNormal (H := V)) := by
  ext x
  rw [Subgroup.mem_comap]
  have h : rho V ⊤ hX ⟨x, Subgroup.mem_top x⟩ = MulAut.conjNormal (H := V) x :=
    BlueprintB2.conjAct_eq_conjNormal V _
  rw [mem_rhoPreimage_top, h]

theorem le_normalizer_comap_conjNormal [V.Normal] {A : Subgroup G} {N : Subgroup (MulAut V)}
    (h : autOn A V ≤ Subgroup.normalizer (N : Set (MulAut V))) :
    A ≤ Subgroup.normalizer ((N.comap (MulAut.conjNormal (H := V)) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hρx : MulAut.conjNormal (H := V) x ∈ autOn A V := by
    rw [autOn_eq_map_conjNormal]
    exact Subgroup.mem_map_of_mem _ hx
  have h1 := Subgroup.mem_normalizer_iff.1 (h hρx) (MulAut.conjNormal (H := V) y)
  rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h1

theorem mem_rhoPreimage_top_iff [V.Normal] (hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G))
    (N : Subgroup (MulAut V)) (x : G) :
    x ∈ rhoPreimage V ⊤ hX N ↔ MulAut.conjNormal (H := V) x ∈ N := by
  rw [rhoPreimage_top_eq_comap, Subgroup.mem_comap]

end Rho

section Simple

theorem isSimpleGroup_alt_five : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])

end Simple

section Normalizer

variable {G : Type} [Group G]

theorem le_normalizer_inf_of_le {A X Y : Subgroup G} (hX : A ≤ Subgroup.normalizer (X : Set G))
    (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    A ≤ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.1 (hX hx) y),
    (Subgroup.mem_normalizer_iff.1 (hY hx) y)]

end Normalizer

section Transport

theorem le_normalizer_of_map_le_map {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {X Y : Subgroup A}
    (h : X.map e.toMonoidHom ≤ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup B) : Set B)) :
    X ≤ Subgroup.normalizer (Y : Set A) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_map_of_mem _ hx)) (e y)
  have h2 : e.toMonoidHom x * e y * (e.toMonoidHom x)⁻¹ = e (x * y * x⁻¹) := by simp
  rw [h2] at h1
  have h3 : e y ∈ Y.map e.toMonoidHom ↔ y ∈ Y := Subgroup.mem_map_iff_mem e.injective
  have h4 : e (x * y * x⁻¹) ∈ Y.map e.toMonoidHom ↔ x * y * x⁻¹ ∈ Y :=
    Subgroup.mem_map_iff_mem e.injective
  rw [h3, h4] at h1
  exact h1

end Transport

end CFSG.QuasithinUnique.Setup.Lift
