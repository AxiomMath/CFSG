module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.CGT.PushingUpLit.BHSSym.SylowTransfer

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

theorem exists_conj_of_stab {m : ℕ} (i₀ : Fin m) (α : Equiv.Perm (Fin m) →* Equiv.Perm (Fin m))
    (hα : ∀ σ, α σ i₀ = i₀ ↔ σ i₀ = i₀) :
    ∃ π : Equiv.Perm (Fin m), π i₀ = i₀ ∧ ∀ σ, α σ = π * σ * π⁻¹ := by
  classical
  set p : Fin m → Fin m := fun x => α (Equiv.swap i₀ x) i₀
  have hinv : ∀ x y, α (Equiv.swap i₀ x) (α (Equiv.swap i₀ x) y) = y := by
    intro x y
    rw [← Equiv.Perm.mul_apply, ← map_mul, Equiv.swap_mul_self, map_one, Equiv.Perm.one_apply]
  have hmul : ∀ (σ : Equiv.Perm (Fin m)) x, p (σ x) = α σ (p x) := by
    intro σ x
    have hfix : (Equiv.swap i₀ (σ x) * σ * Equiv.swap i₀ x) i₀ = i₀ := by
      simp [Equiv.Perm.mul_apply]
    have h1 := (hα _).2 hfix
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
    calc p (σ x) = α (Equiv.swap i₀ (σ x)) i₀ := rfl
      _ = α (Equiv.swap i₀ (σ x)) (α (Equiv.swap i₀ (σ x)) (α σ (p x))) := by rw [h1]
      _ = α σ (p x) := hinv _ _
  have hp0 : p i₀ = i₀ := by
    have h1 : Equiv.swap i₀ i₀ = 1 := Equiv.swap_self i₀
    show α (Equiv.swap i₀ i₀) i₀ = i₀
    rw [h1, map_one]
    rfl
  have hinj : Function.Injective p := by
    intro x y hxy
    have hfix : (Equiv.swap i₀ y * Equiv.swap i₀ x) i₀ = i₀ := by
      rw [← (hα _)]
      rw [map_mul, Equiv.Perm.mul_apply]
      have : α (Equiv.swap i₀ x) i₀ = α (Equiv.swap i₀ y) i₀ := hxy
      rw [this, hinv]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left] at hfix
    exact hfix
  have hbij : Function.Bijective p := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective p hbij, hp0, fun σ => ?_⟩
  refine Equiv.ext fun y => ?_
  set π := Equiv.ofBijective p hbij
  have hy : π (π⁻¹ y) = y := π.apply_symm_apply y
  have hπp : ∀ x, π x = p x := fun x => rfl
  calc α σ y = α σ (π (π⁻¹ y)) := by rw [hy]
    _ = α σ (p (π⁻¹ y)) := by rw [hπp]
    _ = p (σ (π⁻¹ y)) := (hmul σ _).symm
    _ = π (σ (π⁻¹ y)) := (hπp _).symm
    _ = (π * σ * π⁻¹) y := rfl

theorem exists_stab_pGroup {V : Type} [CommGroup V] {T M : Subgroup (MulAut V)}
    (hT2 : IsPGroup 2 ↥T) (hTM : T ≤ M) {E : Subgroup (MulAut V)} {m : ℕ} (h3 : 3 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) (i₀ : Fin m)
    (hM : ∀ x : ↥E, (x : MulAut V) ∈ M ↔ θ x i₀ = i₀) :
    ∃ R : Subgroup (Equiv.Perm (Fin m)), IsPGroup 2 ↥R ∧ (∀ π ∈ R, π i₀ = i₀) ∧
      ∀ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) → ∃ π ∈ R,
        ∀ e e' : ↥E, (e' : MulAut V) = n * e * n⁻¹ → θ e' = π * θ e * π⁻¹ := by
  classical
  set Φ : Subgroup.normalizer (E : Set (MulAut V)) →* MulAut (Equiv.Perm (Fin m)) :=
    (MulAut.congr θ).toMonoidHom.comp E.normalizerMonoidHom
  have hΦapp : ∀ (n : Subgroup.normalizer (E : Set (MulAut V))) (σ : Equiv.Perm (Fin m)),
      Φ n σ = θ (E.normalizerMonoidHom n (θ.symm σ)) := fun n σ => rfl
  set N' : Subgroup (Subgroup.normalizer (E : Set (MulAut V))) := T.subgroupOf _
  set A : Subgroup (MulAut (Equiv.Perm (Fin m))) := N'.map Φ
  set R : Subgroup (Equiv.Perm (Fin m)) :=
    A.comap (MulAut.conj : Equiv.Perm (Fin m) →* MulAut (Equiv.Perm (Fin m))) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin m)) i₀
  refine ⟨R, ?_, fun π hπ => hπ.2, ?_⟩
  · rintro ⟨π, hπ⟩
    obtain ⟨n', hn'N, hn'⟩ := hπ.1
    obtain ⟨k, hk⟩ := hT2 ⟨(n' : MulAut V), Subgroup.mem_subgroupOf.1 hn'N⟩
    have hk' : (n' : MulAut V) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hn'k : n' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    have hconj : MulAut.conj (π ^ 2 ^ k) = 1 := by
      rw [map_pow, ← hn', ← map_pow, hn'k, map_one]
    have hcent : ∀ τ : Equiv.Perm (Fin m), τ * π ^ 2 ^ k = π ^ 2 ^ k * τ := by
      intro τ
      have := congrArg (fun f : MulAut (Equiv.Perm (Fin m)) => f τ) hconj
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    refine ⟨k, Subtype.ext ?_⟩
    simpa using perm_eq_one_of_central h3 hcent
  · intro n hnT hnN
    set n' : Subgroup.normalizer (E : Set (MulAut V)) := ⟨n, hnN⟩ with hn'
    have hα : ∀ σ, Φ n' σ i₀ = i₀ ↔ σ i₀ = i₀ := by
      intro σ
      have hcoe : ((E.normalizerMonoidHom n' (θ.symm σ) : ↥E) : MulAut V) =
          n * (θ.symm σ : MulAut V) * n⁻¹ := by simp [hn']
      rw [hΦapp, ← hM, hcoe, ← Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hTM hnT)), hM]
      simp
    obtain ⟨π, hπ0, hπ⟩ := exists_conj_of_stab i₀ (Φ n').toMonoidHom hα
    have hπR : π ∈ R := by
      refine ⟨⟨n', Subgroup.mem_subgroupOf.2 hnT, ?_⟩, ?_⟩
      · refine MulEquiv.ext fun σ => ?_
        simpa using hπ σ
      · simpa [MulAction.mem_stabilizer_iff] using hπ0
    refine ⟨π, hπR, fun e e' he' => ?_⟩
    have h1 : E.normalizerMonoidHom n' e = e' := Subtype.ext (by simp [hn', he'])
    have h2 : θ e' = Φ n' (θ e) := by rw [hΦapp, θ.symm_apply_apply, h1]
    rw [h2]
    exact hπ _

theorem orbit_eq_of_sym {V : Type} [CommGroup V] {P T M : Subgroup (MulAut V)}
    {ℰ : Set (Subgroup (MulAut V))} (hmin : MinPar P T M) (hleP : ∀ E' ∈ ℰ, E' ≤ P)
    (hconj : ∀ E' ∈ ℰ, ∀ g ∈ P, conjSub g E' ∈ ℰ)
    (hcomm : ∀ E' ∈ ℰ, ∀ E'' ∈ ℰ, E' ≠ E'' → ∀ x ∈ E', ∀ y ∈ E'', x * y = y * x)
    {E : Subgroup (MulAut V)} (hE : E ∈ ℰ)
    (hind : Disjoint E (⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E')) {m : ℕ}
    (θ : ↥E ≃* Equiv.Perm (Fin m)) (i₀ : Fin m)
    (hM : ∀ x : ↥E, (x : MulAut V) ∈ M ↔ θ x i₀ = i₀)
    {O : Set (Fin m)} (hO : i₀ ∉ O) {a : Fin m} (ha : a ∈ O)
    (hinv : ∀ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) → ∃ π ∈ BHSSym.setStab O,
      ∀ e e' : ↥E, (e' : MulAut V) = n * e * n⁻¹ → θ e' = π * θ e * π⁻¹) :
    ∀ c : Fin m, c ≠ i₀ → c ∈ O := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hci, hcO⟩ := hcon
  have hai : a ≠ i₀ := fun h => hO (h ▸ ha)
  set S : Subgroup (Equiv.Perm (Fin m)) := BHSSym.setStab O
  set X : Subgroup (MulAut V) := (S.comap θ.toMonoidHom).map E.subtype
  have hXE : X ≤ E := Subgroup.map_subtype_le _
  have hXmem : ∀ e : ↥E, (e : MulAut V) ∈ X ↔ θ e ∈ S := by
    intro e
    constructor
    · rintro ⟨y, hy, hye⟩
      have : y = e := Subtype.ext hye
      rw [← this]
      exact hy
    · intro he
      exact ⟨e, he, rfl⟩
  have hNX : ∀ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) →
      ∀ x ∈ X, n * x * n⁻¹ ∈ X := by
    intro n hnT hnN x hx
    obtain ⟨π, hπO, hπ⟩ := hinv n hnT hnN
    have hxE : x ∈ E := hXE hx
    have hxE' : n * x * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hnN x).1 hxE
    have h1 := hπ ⟨x, hxE⟩ ⟨n * x * n⁻¹, hxE'⟩ rfl
    have h2 : θ ⟨x, hxE⟩ ∈ S := (hXmem ⟨x, hxE⟩).1 hx
    refine (hXmem ⟨_, hxE'⟩).2 ?_
    rw [h1]
    exact S.mul_mem (S.mul_mem hπO h2) (S.inv_mem hπO)
  have hNX' : ∀ n ∈ T, n ∈ Subgroup.normalizer (E : Set (MulAut V)) → conjSub n X = X := by
    intro n hnT hnN
    have hnT' : n⁻¹ ∈ T := T.inv_mem hnT
    have hnN' : n⁻¹ ∈ Subgroup.normalizer (E : Set (MulAut V)) := Subgroup.inv_mem _ hnN
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_conjSub_iff] at hx
      have := hNX n hnT hnN _ hx
      simpa [mul_assoc] using this
    · rw [mem_conjSub_iff]
      have := hNX n⁻¹ hnT' hnN' x hx
      simpa [mul_assoc] using this
  set 𝒳 : Set (Subgroup (MulAut V)) := {A | ∃ t ∈ T, A = conjSub t X}
  set X' : Subgroup (MulAut V) := ⨆ A ∈ 𝒳, A
  have hXX' : X ≤ X' :=
    le_iSup₂_of_le (f := fun A (_ : A ∈ 𝒳) => A) X ⟨1, T.one_mem, (conjSub_one X).symm⟩ le_rfl
  have hTn : T ≤ Subgroup.normalizer (X' : Set (MulAut V)) := by
    refine le_normalizer_iSup ?_
    rintro A ⟨t, ht, rfl⟩ g hg
    exact ⟨g * t, T.mul_mem hg ht, (conjSub_mul g t X).symm⟩
  set F : Subgroup (MulAut V) := ⨆ E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}, E'
  have hFcent : F ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
    refine iSup₂_le fun E' hE' => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm E hE E' hE'.1 (Ne.symm hE'.2) x hx y hy
  have hFnormX : F ≤ Subgroup.normalizer (X : Set (MulAut V)) :=
    hFcent.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hXE)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hX'le : X' ≤ X ⊔ F := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨t, ht, rfl⟩ := hA
    by_cases htN : t ∈ Subgroup.normalizer (E : Set (MulAut V))
    · rw [hNX' t ht htN]
      exact le_sup_left
    · have hne : conjSub t E ≠ E := fun h' => htN (Subgroup.mem_normalizer_iff_map_conj_eq.2 h')
      refine le_sup_of_le_right ((conjSub_mono t hXE).trans ?_)
      exact le_iSup₂_of_le (f := fun (E' : Subgroup (MulAut V))
        (_ : E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ E}) => E') (conjSub t E)
        ⟨hconj E hE t (hmin.T_le ht), hne⟩ le_rfl
  have hEX' : ∀ e ∈ E, e ∈ X' → e ∈ X := by
    intro e heE heX'
    obtain ⟨x, hx, f, hf, hxf⟩ := exists_mul_of_mem_sup hFnormX (hX'le heX')
    have hfE : f ∈ E := by
      have : f = x⁻¹ * e := by rw [hxf]; group
      rw [this]
      exact E.mul_mem (E.inv_mem (hXE hx)) heE
    have hf1 : f = 1 := Subgroup.disjoint_def.1 hind hfE hf
    rw [hxf, hf1, mul_one]
    exact hx
  have hX'P : X' ≤ P := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨t, ht, rfl⟩ := hA
    exact (conjSub_mono t hXE).trans (hleP _ (hconj E hE t (hmin.T_le ht)))
  set Y : Subgroup (MulAut V) := P ⊓ Subgroup.normalizer (X' : Set (MulAut V))
  have hTY : T ≤ Y := le_inf hmin.T_le hTn
  have hX'Y : X' ≤ Y := le_inf hX'P Subgroup.le_normalizer
  have hsw : Equiv.swap i₀ c ∈ S := by
    intro x
    by_cases h1 : x = i₀
    · subst h1
      simp [hO, hcO]
    · by_cases h2 : x = c
      · subst h2
        simp [hO, hcO]
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hEnot : ¬ E ≤ Subgroup.normalizer (X' : Set (MulAut V)) := by
    intro hEn
    have hXnorm : ∀ e x : ↥E, θ x ∈ S → θ (e * x * e⁻¹) ∈ S := by
      intro e x hx
      have hxX : (x : MulAut V) ∈ X := (hXmem x).2 hx
      have h1 : (e : MulAut V) * x * (e : MulAut V)⁻¹ ∈ X' :=
        (Subgroup.mem_normalizer_iff.1 (hEn e.2) x).1 (hXX' hxX)
      have h2 : ((e * x * e⁻¹ : ↥E) : MulAut V) ∈ E := (e * x * e⁻¹).2
      exact (hXmem _).1 (hEX' _ h2 h1)
    have hSnorm : ∀ σ τ : Equiv.Perm (Fin m), τ ∈ S → σ * τ * σ⁻¹ ∈ S := by
      intro σ τ hτ
      have := hXnorm (θ.symm σ) (θ.symm τ) (by simpa using hτ)
      simpa using this
    have h3 := hSnorm (Equiv.swap c a) _ hsw a
    have h4 : (Equiv.swap c a * Equiv.swap i₀ c * (Equiv.swap c a)⁻¹) a = i₀ := by
      rw [Equiv.swap_inv]
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hci) hai.symm]
    rw [h4] at h3
    exact hO (h3.2 ha)
  have hYP : Y < P := by
    refine lt_of_le_of_ne inf_le_left fun hYP => hEnot ?_
    calc E ≤ P := hleP E hE
      _ = Y := hYP.symm
      _ ≤ Subgroup.normalizer (X' : Set (MulAut V)) := inf_le_right
  have hXM : X ≤ M := hXX'.trans (hX'Y.trans (hmin.max Y hTY hYP))
  have he₀ : ((θ.symm (Equiv.swap i₀ c) : ↥E) : MulAut V) ∈ X := (hXmem _).2 (by simpa using hsw)
  have := (hM (θ.symm (Equiv.swap i₀ c))).1 (hXM he₀)
  simp at this
  exact hci this

variable {V : Type} [CommGroup V] [Finite V]

theorem FiveFive.two_pow_of_sym {P T M : Subgroup (MulAut V)}
    {ℰ : Set (Subgroup (MulAut V))} (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)
    (hF : FiveFive P T M ℰ) {E : Subgroup (MulAut V)} (hE : E ∈ ℰ) {m : ℕ} (h3 : 3 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) (i₀ : Fin m)
    (hM : ∀ x : ↥E, (x : MulAut V) ∈ M ↔ θ x i₀ = i₀) : ∃ k : ℕ, m = 2 ^ k + 1 := by
  obtain ⟨R, hR2, hRfix, hR⟩ := exists_stab_pGroup h.minpar.syl.2.1 h.minpar.le_M h3 θ i₀ hM
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨x₁, hx₁⟩ := exists_ne i₀
  have hOstab : ∀ π ∈ R, π ∈ BHSSym.setStab (MulAction.orbit R x₁) := by
    intro π hπ x
    set g : R := ⟨π, hπ⟩
    have hgx : g • x = π x := rfl
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hgx] at hx
      have := MulAction.mem_orbit_of_mem_orbit g⁻¹ hx
      rwa [inv_smul_smul] at this
    · rw [← hgx]
      exact MulAction.mem_orbit_of_mem_orbit g hx
  have hi₀O : i₀ ∉ MulAction.orbit R x₁ := by
    rintro ⟨g, hg⟩
    apply hx₁
    have h1 : (g : Equiv.Perm (Fin m)) x₁ = i₀ := hg
    have h2 : (g : Equiv.Perm (Fin m)) i₀ = i₀ := hRfix g g.2
    exact (g : Equiv.Perm (Fin m)).injective (h1.trans h2.symm)
  have hcov : ∀ c : Fin m, c ≠ i₀ → c ∈ MulAction.orbit R x₁ :=
    orbit_eq_of_sym h.minpar (fun E' hE' => hF.le_P h hV hE') hF.conj_mem hF.comm hE
      (hF.indep E hE) θ i₀ hM hi₀O (MulAction.mem_orbit_self x₁) fun n hnT hnN => by
        obtain ⟨π, hπR, hπ⟩ := hR n hnT hnN
        exact ⟨π, hOstab π hπR, hπ⟩
  obtain ⟨k, hk⟩ := IsPGroup.card_orbit hR2 x₁
  have heq : MulAction.orbit R x₁ = {y | y ≠ i₀} :=
    Set.ext fun y => ⟨fun hy hyi => hi₀O (hyi ▸ hy), fun hy => hcov y hy⟩
  rw [heq] at hk
  have hcard : Nat.card ↥{y : Fin m | y ≠ i₀} = m - 1 := by
    have h1 : Nat.card ↥{y : Fin m | y ≠ i₀} = Nat.card {x : Fin m // ¬ x = i₀} := rfl
    rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    simp
  exact ⟨k, by omega⟩

end CFSG.CGT.PushingUpLit.BHS5
