module

public import CFSG.HardMathSupport.Malle.OvergroupTransport.Max
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4NormalizerOrder
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizerMax
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
public import CFSG.RankThree.PartOne.SEITZ12.Main

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.AGLEmbedding CFSG.Open CFSG.RankThree.PartOne.K1214

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_omega_one (hsh : SylowShape 5 2 2 G) (P : Sylow 5 G) :
    ∃ Z : Subgroup G, (∀ y, y ∈ Z ↔ y ∈ (P : Subgroup G) ∧ y ^ 5 = 1) ∧
      (∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a) ∧
      Z ≤ (P : Subgroup G) ∧ IsElemAbelian 5 Z ∧ Nat.card Z = 5 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hsh (P : Subgroup G) P.isPGroup' P.not_dvd_index
  have e' : (P : Subgroup G) ≃* Hc := e
  let E₀ : Subgroup Hc := (powMonoidHom 5 : Hc →* Hc).ker
  let Z : Subgroup G := (E₀.map e'.symm.toMonoidHom).map (P : Subgroup G).subtype
  have hmem : ∀ x : G, x ∈ Z ↔ ∃ v ∈ E₀, ((e'.symm v : (P : Subgroup G)) : G) = x := by
    intro x
    simp only [Z, Subgroup.mem_map, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hv5 : ∀ v ∈ E₀, v ^ 5 = 1 := fun v hv => by
    simpa [E₀, MonoidHom.mem_ker, powMonoidHom_apply] using hv
  have hZP : Z ≤ (P : Subgroup G) := by
    rintro x hx
    obtain ⟨v, -, rfl⟩ := (hmem x).1 hx
    exact (e'.symm v).2
  have hZ5 : ∀ x ∈ Z, x ^ 5 = 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := (hmem x).1 hx
    rw [← Subgroup.coe_pow, ← map_pow, hv5 v hv, map_one]
    rfl
  refine ⟨Z, fun y => ⟨fun hy => ⟨hZP hy, hZ5 y hy⟩, fun ⟨hy, h5⟩ => ?_⟩,
    comm_of_homocyclic e', hZP, (isElemAbelian_iff Z).2 ⟨?_, hZ5⟩, ?_⟩
  · refine (hmem y).2 ⟨e' ⟨y, hy⟩, ?_, by simp⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    have : (⟨y, hy⟩ : (P : Subgroup G)) ^ 5 = 1 := Subtype.ext (by simpa using h5)
    rw [this, map_one]
  · intro a ha b hb
    obtain ⟨v, -, rfl⟩ := (hmem a).1 ha
    obtain ⟨w, -, rfl⟩ := (hmem b).1 hb
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, mul_comm v w]
  · rw [Subgroup.card_map_of_injective (Subtype.val_injective),
      Subgroup.card_map_of_injective e'.symm.injective]
    exact card_pow_five_ker

theorem centralizer_transitive_of_plane_data (hsh : SylowShape 5 2 2 G)
    (hC : ∀ (P : Sylow 5 G) (E : Subgroup G), E ≤ (P : Subgroup G) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set G) = (P : Subgroup G))
    (hplane : ∃ (R : Subgroup G) (i j h t : G), (∀ r ∈ R, r ^ 5 = 1) ∧ Nat.card R = 5 ^ 2 ∧
      CFSG.Quasithin.B45Tor.IsGL23Data R i j h t)
    (P : Sylow 5 G) {Z : Subgroup G}
    (hZ : ∀ y, y ∈ Z ↔ y ∈ (P : Subgroup G) ∧ y ^ 5 = 1) (hZP : Z ≤ (P : Subgroup G))
    (hZe : IsElemAbelian 5 Z) (hZc : Nat.card Z = 5 ^ 2) :
    ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ Z, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), ∀ g : G,
        g ∈ Subgroup.centralizer ({y} : Set G) →
          n⁻¹ * g * n ∈ Subgroup.centralizer ({x} : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨R, i, j, h, t, hR5, hRc, hd⟩ := hplane
  have hshT : SylowShape 5 2 2 (⊤ : Subgroup G) := SylowShape.of_mulEquiv Subgroup.topEquiv hsh
  obtain ⟨g₀, hg₀⟩ := exists_conj_eq_plane (⊤ : Subgroup G) hshT P Z (le_inf hZP le_top) hZe.2 hZc
    R le_top hR5 hRc
  have hGL : CFSG.Quasithin.B45Tor.IsGL23Data Z ((MulAut.conj g₀).toMonoidHom i)
      ((MulAut.conj g₀).toMonoidHom j) ((MulAut.conj g₀).toMonoidHom h)
      ((MulAut.conj g₀).toMonoidHom t) := by
    rw [hg₀]; exact isGL23Data_map _ hd
  have hQ := hGL.toIsQ8Data
  have hNZ : Subgroup.normalizer (Z : Set G) = Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    normalizer_plane_eq hsh hC P hZP hZe hZc
  intro x hx hx1 y hy hy1
  have hx5 : x ^ 5 = 1 := ((hZ x).1 hx).2
  have hy5 : y ^ 5 = 1 := ((hZ y).1 hy).2
  have hFc : ∀ w : G, w ≠ 1 → w ^ 5 = 1 → Nat.card (Subgroup.zpowers w) = 5 := by
    intro w hw1 hw5
    rw [Nat.card_zpowers, orderOf_eq_prime hw5 hw1]
  have hFZ : ∀ w ∈ Z, Subgroup.zpowers w ≤ Z := fun w hw => (Subgroup.zpowers_le).2 hw
  obtain ⟨n, hn, hnF⟩ := lines_transitive_of_isQ8Data hZe hZc hQ (Subgroup.zpowers x)
    (Subgroup.zpowers y) (hFZ x hx) (hFZ y hy) (hFc x hx1 hx5) (hFc y hy1 hy5)
  refine ⟨n, hNZ ▸ hn, fun g hg => ?_⟩
  have hmem : n * x * n⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hnF]
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hyg : Commute y g := (Subgroup.mem_centralizer_iff.1 hg y rfl)
  have hcomm : (n * x * n⁻¹) * g = g * (n * x * n⁻¹) := by
    rw [← hk]; exact ((hyg.zpow_left k).eq)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  calc x * (n⁻¹ * g * n) = n⁻¹ * ((n * x * n⁻¹) * g) * n := by group
    _ = n⁻¹ * (g * (n * x * n⁻¹)) * n := by rw [hcomm]
    _ = n⁻¹ * g * n * x := by group

theorem map_centralizer_equiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) (S : Set A) :
    (Subgroup.centralizer S).map f.toMonoidHom = Subgroup.centralizer (f '' S) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    show f s * f g = f g * f s
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hg s hs]
  · intro hy
    refine ⟨f.symm y, ?_, by simp⟩
    show f.symm y ∈ Subgroup.centralizer S
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.1 hy (f s) ⟨s, hs, rfl⟩

theorem conj_injective_of_simple {K : Type*} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · have hgc : g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut K => φ z) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [h] at hgc
    simpa using hgc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

end Generic

section Group


theorem reeF4_planeData {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d)) :
    (∀ (P : Sylow 5 K) (E : Subgroup K), E ≤ (P : Subgroup K) → IsElemAbelian 5 E →
      Nat.card E = 5 ^ 2 → Subgroup.centralizer (E : Set K) = (P : Subgroup K)) ∧
    ∃ (R : Subgroup K) (i j h t : K), (∀ r ∈ R, r ^ 5 = 1) ∧ Nat.card R = 5 ^ 2 ∧
      CFSG.Quasithin.B45Tor.IsGL23Data R i j h t := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, _, hF, ⟨f⟩⟩ := exists_reeGamma_model hd e
  have : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2) := Subtype.finite
  refine ⟨fun P E hEP hE hEc => ?_, ?_⟩
  · let P' : Sylow 5 (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2) :=
      P.mapSurjective (f := f.toMonoidHom) f.surjective
    have hP' : (P' : Subgroup _) = (P : Subgroup K).map f.toMonoidHom := rfl
    have h1 := centralizer_plane_eq_sylow hF P' (E.map f.toMonoidHom)
      (hP' ▸ Subgroup.map_mono hEP) (isElemAbelian_map' _ hE)
      (by rw [Subgroup.card_map_of_injective f.injective, hEc])
    apply Subgroup.map_injective f.injective (f := f.toMonoidHom)
    rw [map_centralizer_equiv, ← hP']
    rw [← h1]
    congr 2
  · obtain ⟨R, i, j, h, t, -, hR5, hRc, hGL, -, -⟩ :=
      CFSG.Quasithin.B45Tor.exists_reePlane (K := F) (a := 2) (by norm_num) hF
        (p := 5) Nat.prime_five (by norm_num) (Or.inl (by norm_num))
    refine ⟨R.map f.symm.toMonoidHom, f.symm i, f.symm j, f.symm h, f.symm t, ?_, ?_,
      isGL23Data_map f.symm.toMonoidHom hGL⟩
    · rintro _ ⟨r, hr, rfl⟩
      show f.symm r ^ 5 = 1
      rw [← map_pow, hR5 r hr, map_one]
    · rw [Subgroup.card_map_of_injective f.symm.injective, hRc]

theorem reeF4_maximal {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CatGroup d)) (P : Sylow 5 K) {Z : Subgroup K}
    (hZP : Z ≤ (P : Subgroup K)) (hZe : IsElemAbelian 5 Z) :
    ∀ x ∈ Z, x ≠ 1 → ∀ H : Subgroup K,
      Subgroup.normalizer ((P : Subgroup K) : Set K) ⊓ Subgroup.centralizer ({x} : Set K) ≤ H →
        H ≤ Subgroup.centralizer ({x} : Set K) →
          H = Subgroup.normalizer ((P : Subgroup K) : Set K) ⊓
              Subgroup.centralizer ({x} : Set K) ∨
            H = Subgroup.centralizer ({x} : Set K) := by
  intro x hxZ hx1 H hH₁ hH₂
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨F, _, _, _, hF, ⟨f⟩⟩ := exists_reeGamma_model hd e
  have : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2) := Subtype.finite
  let P' : Sylow 5 (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2) :=
    P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hP' : (P' : Subgroup _) = (P : Subgroup K).map f.toMonoidHom := rfl
  have hN : Subgroup.normalizer ((P' : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) :
      Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) =
      (Subgroup.normalizer ((P : Subgroup K) : Set K)).map f.toMonoidHom := by
    rw [hP', Subgroup.map_equiv_normalizer_eq]
  have hC : Subgroup.centralizer ({f x} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) =
      (Subgroup.centralizer ({x} : Set K)).map f.toMonoidHom := by
    rw [map_centralizer_equiv, Set.image_singleton]
  have hinf : Subgroup.normalizer ((P' : Subgroup (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) :
      Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) ⊓
      Subgroup.centralizer ({f x} : Set (CFSG.LieType.Ree.ReeTag.F4.reeGamma F 2)) =
      (Subgroup.normalizer ((P : Subgroup K) : Set K) ⊓
        Subgroup.centralizer ({x} : Set K)).map f.toMonoidHom := by
    rw [hN, hC, Subgroup.map_inf_eq _ _ _ f.injective]
  have hmax := centralizer_normalizer_maximal hF P' (Z.map f.toMonoidHom)
    (hP' ▸ Subgroup.map_mono hZP) (isElemAbelian_map' _ hZe) (f x)
    (Subgroup.mem_map_of_mem _ hxZ) (fun h => hx1 (f.injective (by rw [h, map_one])))
    (H := H.map f.toMonoidHom) (by rw [hinf]; exact Subgroup.map_mono hH₁)
    (by rw [hC]; exact Subgroup.map_mono hH₂)
  rcases hmax with h | h
  · left
    apply Subgroup.map_injective f.injective (f := f.toMonoidHom)
    rw [h, hinf]
  · right
    apply Subgroup.map_injective f.injective (f := f.toMonoidHom)
    rw [h, hC]

end Group

section Generation


theorem reeF4_generation {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeFFourFiveIndex d) (e : Nonempty (K ≃* CatGroup d)) (Z : Subgroup K)
    (hZe : IsElemAbelian 5 Z) (hZc : Nat.card Z = 5 ^ 2) :
    Subgroup.closure {k : K | ∃ x ∈ Z, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e₀⟩ := e
  have hd' : d.1 = .reeF4 2 := hd
  have hsimpleC : IsSimpleGroup (CatGroup d) :=
    CFSG.AGLEmbedding.isSimpleGroup_of_catGroup_reeF4 hd'
  have : IsSimpleGroup K := e₀.isSimpleGroup
  have hcard : Nat.card K = CFSG.Open.ordTwistedF4 (2 ^ (2 * 2 + 1)) := by
    rw [Nat.card_congr e₀.toEquiv]
    exact CFSG.AGLEmbedding.card_catGroup_reeF4 hd'
  have hnab : ∃ a b : K, a * b ≠ b * a :=
    CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_two
      (by rw [hcard]; decide)
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.reeF4 2) := by
    obtain ⟨d₁, hv⟩ := d
    simp only at hd'
    subst hd'
    exact ⟨hv, ⟨e₀⟩⟩
  have hinj := conj_injective_of_simple hnab
  set E : Subgroup (MulAut K) := Z.map (MulAut.conj : K →* MulAut K) with hE
  have hEcomm : IsMulCommutative E := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, x, hx, rfl⟩ := a
    obtain ⟨b, y, hy, rfl⟩ := b
    apply Subtype.ext
    show MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x
    rw [← map_mul, ← map_mul, ((isElemAbelian_iff Z).1 hZe).1 x hx y hy]
  have hEexp : Monoid.exponent E ∣ 5 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨a, x, hx, rfl⟩
    apply Subtype.ext
    show (MulAut.conj x) ^ 5 = 1
    rw [← map_pow, hZe.2 x hx, map_one]
  have hEel : CFSG.IsElementaryAbelian 5 E :=
    { toIsMulCommutative := hEcomm, exponent_dvd_p := hEexp }
  have hEcard : Nat.card E = 5 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hinj, hZc]
  have hinner : ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hchar : (5 : ℕ) ≠ (TauCeti.LieTypeIndex.reeF4 2).characteristic := by
    rw [TauCeti.LieTypeIndex.characteristic_reeF4]
    norm_num
  have hseitz := CFSG.RankThree.PartOne.SEITZ12.exc2F4NonsplitPhi4_holds 2 K hnab hiso 5
    Nat.prime_five (le_refl 5) hchar (by norm_num) E hEel hEcard hinner
  have hset : {k : K | ∃ F : Subgroup (MulAut K), F ≤ E ∧ F ≠ ⊥ ∧ ∀ φ ∈ F, φ k = k} =
      {k : K | ∃ x ∈ Z, x ≠ 1 ∧ k * x = x * k} := by
    ext k
    constructor
    · rintro ⟨F', hFE, hF0, hFk⟩
      obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hF0
      obtain ⟨x, hxZ, hx⟩ := Subgroup.mem_map.1 (hFE a.2)
      refine ⟨x, hxZ, fun h => ha (Subtype.ext ?_), ?_⟩
      · rw [← hx, h, map_one]; rfl
      · have h1 := hFk a a.2
        rw [← hx] at h1
        simp only [MulAut.conj_apply] at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
    · rintro ⟨x, hxZ, hx1, hxk⟩
      refine ⟨Subgroup.zpowers (MulAut.conj x), ?_, ?_, ?_⟩
      · exact (Subgroup.zpowers_le).2 (Subgroup.mem_map.2 ⟨x, hxZ, rfl⟩)
      · intro h
        have h1 : (MulAut.conj x : MulAut K) ∈ (⊥ : Subgroup (MulAut K)) :=
          h ▸ Subgroup.mem_zpowers _
        rw [Subgroup.mem_bot] at h1
        exact hx1 (hinj (by rw [h1, map_one]))
      · intro φ hφ
        have hst : Subgroup.zpowers (MulAut.conj x) ≤ MulAction.stabilizer (MulAut K) k := by
          rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
          show x * k * x⁻¹ = k
          rw [mul_inv_eq_iff_eq_mul, hxk]
        exact MulAction.mem_stabilizer_iff.1 (hst hφ)
  rcases hseitz with h | ⟨-, h | h⟩
  · rw [hset] at h
    exact h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

end Generation

theorem reeF4SocleLineData_of_certs :
    CFSG.HardMathSupport.Malle.OvergroupTransport.ReeF4SocleLineData := by
  intro K _ _ d hd e P
  have hsh : SylowShape 5 2 2 K := sylowShape_five_of_catGroup hd e
  obtain ⟨Z, hZ, hab, hZP, hZe, hZc⟩ := exists_omega_one hsh P
  obtain ⟨hC, hplane⟩ := reeF4_planeData hd e
  exact ⟨Z, hZ, hab, hZc, reeF4_maximal hd e P hZP hZe,
    centralizer_transitive_of_plane_data hsh hC hplane P hZ hZP hZe hZc⟩

end CFSG.HardMathSupport.Malle.LocalAction
