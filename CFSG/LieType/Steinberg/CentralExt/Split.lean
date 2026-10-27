module

public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LieType.Steinberg.Presentation
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.CentralExt

universe u w

section FreeSub

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Group K] {Φ : RootSystem ι}
  {X : (ι → ℤ) → Subgroup K} {G : Type*} [Group G] {S : Set (ι → ℤ)} {Q : Subgroup K}

theorem lift_eq_of_mem_freeSub (hQ : ∀ γ ∈ S, X γ ≤ Q) (s : Q →* G) {φ : Symbol Φ X → G}
    (hφ : ∀ (t : Symbol Φ X) (ht : t.1.1 ∈ S), φ t = s ⟨t.1.2, hQ _ ht t.2.2⟩)
    {v : FreeSt Φ X} (hv : v ∈ freeSub Φ X S) :
    ∃ h : piF Φ X v ∈ Q, FreeGroup.lift φ v = s ⟨piF Φ X v, h⟩ := by
  induction hv using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨by simpa [piF] using hQ _ ht t.2.2, by simpa [piF] using hφ t ht⟩
  | one =>
    refine ⟨by simp, ?_⟩
    rw [map_one]
    exact (map_one s).symm
  | mul u v _ _ hu hv =>
    obtain ⟨hu, hu'⟩ := hu
    obtain ⟨hv, hv'⟩ := hv
    refine ⟨by simpa using Q.mul_mem hu hv, ?_⟩
    rw [map_mul, hu', hv', ← map_mul]
    exact congrArg s (Subtype.ext (map_mul (piF Φ X) u v).symm)
  | inv v _ hv =>
    obtain ⟨hv, hv'⟩ := hv
    refine ⟨by simpa using Q.inv_mem hv, ?_⟩
    rw [map_inv, hv', ← map_inv]
    exact congrArg s (Subtype.ext (map_inv (piF Φ X) v).symm)

theorem lift_eq_one_of_mem_freeSub (hQ : ∀ γ ∈ S, X γ ≤ Q) (s : Q →* G)
    {φ : Symbol Φ X → G}
    (hφ : ∀ (t : Symbol Φ X) (ht : t.1.1 ∈ S), φ t = s ⟨t.1.2, hQ _ ht t.2.2⟩)
    {v : FreeSt Φ X} (hv : v ∈ freeSub Φ X S) (h1 : piF Φ X v = 1) :
    FreeGroup.lift φ v = 1 := by
  obtain ⟨h, hv'⟩ := lift_eq_of_mem_freeSub hQ s hφ hv
  rw [hv', show (⟨piF Φ X v, h⟩ : Q) = 1 from Subtype.ext h1, map_one]

end FreeSub

section Section

variable {E K : Type*} [Group E] [Group K] {π : E →* K}

@[expose] noncomputable def kerProdRangeHom (hker : π.ker ≤ Subgroup.center E) (σ : K →* E) :
    π.ker × σ.range →* E :=
  MonoidHom.noncommCoprod π.ker.subtype σ.range.subtype fun c x =>
    (Subgroup.mem_center_iff.1 (hker c.2) x).symm

theorem kerProdRangeHom_apply (hker : π.ker ≤ Subgroup.center E) (σ : K →* E)
    (x : π.ker × σ.range) : kerProdRangeHom hker σ x = (x.1 : E) * x.2 :=
  rfl

theorem kerProdRangeHom_bijective (hker : π.ker ≤ Subgroup.center E) {σ : K →* E}
    (hσ : ∀ x, π (σ x) = x) : Function.Bijective (kerProdRangeHom hker σ) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun ⟨c, y⟩ h => ?_, fun e => ?_⟩
  · obtain ⟨x, hx⟩ := y.2
    have h' : (c : E) * y = 1 := h
    have hy : (y : E) = 1 := by
      have := congrArg π h'
      rw [map_mul, (MonoidHom.mem_ker).1 c.2, one_mul, map_one, ← hx, hσ] at this
      rw [← hx, this, map_one]
    rw [hy, mul_one] at h'
    exact Prod.ext (Subtype.ext h') (Subtype.ext hy)
  · have hc : e * (σ (π e))⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    exact ⟨(⟨_, hc⟩, ⟨σ (π e), π e, rfl⟩), inv_mul_cancel_right e _⟩

@[expose] noncomputable def kerProdRangeEquiv (hker : π.ker ≤ Subgroup.center E) {σ : K →* E}
    (hσ : ∀ x, π (σ x) = x) : π.ker × σ.range ≃* E :=
  MulEquiv.ofBijective (kerProdRangeHom hker σ) (kerProdRangeHom_bijective hker hσ)

theorem kerProdRangeEquiv_apply (hker : π.ker ≤ Subgroup.center E) {σ : K →* E}
    (hσ : ∀ x, π (σ x) = x) (x : π.ker × σ.range) :
    kerProdRangeEquiv hker hσ x = (x.1 : E) * x.2 :=
  rfl

theorem exists_section_mulEquiv_of_existsUnique (hker : π.ker ≤ Subgroup.center E)
    (h : ∃! σ : K →* E, ∀ x, π (σ x) = x) :
    ∃ σ : K →* E, (∀ x, π (σ x) = x) ∧ (∀ τ : K →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  obtain ⟨σ, hσ, huniq⟩ := h
  exact ⟨σ, hσ, huniq, kerProdRangeEquiv hker hσ, kerProdRangeEquiv_apply hker hσ⟩

theorem exists_lift_of_injective {M : Type*} [Group M] {L : Subgroup K} {ρ : M →* K}
    (hρ : Function.Injective ρ) (hL : L ≤ ρ.range) {ρ' : M →* E} (hρ' : ∀ g, π (ρ' g) = ρ g) :
    ∃ φ : L →* E, ∀ x, π (φ x) = x := by
  refine ⟨ρ'.comp ((MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (Subgroup.inclusion hL)),
    fun x => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hρ']
  rw [← MonoidHom.ofInjective_apply hρ, MulEquiv.apply_symm_apply, Subgroup.coe_inclusion]

end Section

section SL2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Group K] {Φ : RootSystem ι}
  {X : (ι → ℤ) → Subgroup K} {k : Type*} [Field k] {x : (ι → ℤ) → k → K}

theorem rankOne_le_range_of_sl2 (hx : IsParametrization (Φ := Φ) X x) (i : ι)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c) : rankOne X i ≤ ρ.range := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, rfl⟩ := ((hx _ (Φ.single_mem i)).1 g).1 hg
    exact ⟨sl2Upper c, hU c⟩
  · obtain ⟨c, rfl⟩ := ((hx _ (Φ.neg_mem _ (Φ.single_mem i))).1 g).1 hg
    exact ⟨sl2Lower c, hL c⟩

end SL2

section Splitting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type u} [Group K] {Φ : RootSystem ι}
  {X : (ι → ℤ) → Subgroup K} {p : ℕ} [Fact p.Prime] {E : Type w} [Group E] [Finite E]
  {π : E →* K}

theorem hom_ext_of_iSup_eq_top {G : Type*} [Group G] (hgen : ⨆ γ ∈ Φ.roots, X γ = ⊤)
    {f g : K →* G} (h : ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, f x = g x) : f = g := by
  have hle : ⨆ γ ∈ Φ.roots, X γ ≤ f.eqLocus g := iSup₂_le fun γ hγ x hx => h γ hγ x hx
  rw [hgen] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

theorem existsUnique_section_of_presentationA (hA : PresentationA.{_, u, w} Φ X)
    (hcone : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ¬ IsNegMultiple α β →
      IsPGroup p ↥(⨆ γ ∈ cone Φ.roots α β, X γ))
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker)
    (hrank : ∀ i, ∃ φ : ↥(rankOne X i) →* E, ∀ x, π (φ x) = x) :
    ∃! σ : K →* E, ∀ x, π (σ x) = x := by
  have hpe : ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, ∃ n : ℕ, orderOf x = p ^ n := fun γ hγ x hx => by
    have hγ0 : γ ≠ 0 := fun h => Φ.zero_notMem (h ▸ hγ)
    refine exists_orderOf_eq_pow_of_mem ((hcone γ hγ γ hγ (not_isNegMultiple_self hγ0)).to_le
      (le_iSup₂_of_le (f := fun δ (_ : δ ∈ cone Φ.roots γ γ) => X δ) γ ⟨hγ, 1, 0, by simp⟩
        le_rfl)) ⟨x, hx⟩
  have hsec : ∀ σ : K →* E, (∀ x, π (σ x) = x) → ∀ γ ∈ Φ.roots, ∀ x ∈ X γ,
      σ x = pLift p π x := fun σ hσ γ hγ x hx =>
    (pLift_unique hker hC (hσ x) (exists_orderOf_map_eq_pow σ (hpe γ hγ x hx))).symm
  have hφ : ∀ w ∈ rel1 Φ X ∪ rel2 Φ X,
      FreeGroup.lift (fun t : Symbol Φ X => pLift p π t.1.2) w = 1 := by
    rintro w (⟨α, hα, β, hβ, hαβ, hw, hw1⟩ | ⟨i, hw, hw1⟩)
    · exact lift_eq_one_of_mem_freeSub (fun γ hγ => le_iSup₂_of_le γ hγ le_rfl)
        (pLiftHom hπ hker hC (hcone α hα β hβ hαβ)) (fun t ht => rfl) hw hw1
    · obtain ⟨φ, hφ⟩ := hrank i
      refine lift_eq_one_of_mem_freeSub (Q := rankOne X i) (fun γ hγ => ?_) φ
        (fun t ht => ?_) hw hw1
      · rcases hγ with rfl | rfl
        exacts [le_sup_left, le_sup_right]
      · refine pLift_unique hker hC (hφ _) (exists_orderOf_map_eq_pow φ ?_)
        obtain ⟨m, hm⟩ := hpe _ t.2.1 _ t.2.2
        exact ⟨m, by rw [← Subgroup.orderOf_coe]; exact hm⟩
  obtain ⟨σ, hσ, -⟩ := hA.2.2 E _ hφ
  have hπσ : π.comp σ = MonoidHom.id K := hom_ext_of_iSup_eq_top hA.1 fun γ hγ x hx => by
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hσ ⟨(γ, x), hγ, hx⟩,
      map_pLift hπ hC (hpe γ hγ x hx)]
  have hσ' : ∀ x, π (σ x) = x := fun x => DFunLike.congr_fun hπσ x
  refine ⟨σ, hσ', fun τ hτ => hom_ext_of_iSup_eq_top hA.1 fun γ hγ x hx => ?_⟩
  rw [hsec τ hτ γ hγ x hx, hsec σ hσ' γ hγ x hx]

end Splitting

section Universal

variable {K : Type u} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {p : ℕ} [Fact p.Prime] {E : Type w} [Group E] [Finite E]
  {π : E →* K}

theorem existsUnique_section_of_rankOne_lift
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker)
    (hrank : ∀ i, ∃ φ : ↥(rankOne D.rootGroup i) →* E, ∀ x, π (φ x) = x) :
    ∃! σ : K →* E, ∀ x, π (σ x) = x :=
  existsUnique_section_of_presentationA (presentationA_of hct hext)
    (fun _ hα _ hβ h => isPGroup_iSup_cone hext hX hα hβ h) hπ hker hC hrank

theorem existsUnique_section_of_sl2_lift {k : Type*} [Field k] [CharP k p]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hρ : ∀ i, ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective ρ ∧
      (∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c) ∧ ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker)
    (hlift : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K,
      ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) k →* E, ∀ g, π (ρ' g) = ρ g) :
    ∃! σ : K →* E, ∀ x, π (σ x) = x := by
  refine existsUnique_section_of_rankOne_lift hct hext
    (fun γ hγ => isPGroup_of_isParametrization hx hγ) hπ hker hC fun i => ?_
  obtain ⟨ρ, hρi, hU, hL⟩ := hρ i
  obtain ⟨ρ', hρ'⟩ := hlift ρ
  exact exists_lift_of_injective hρi (rankOne_le_range_of_sl2 hx i hU hL) hρ'

end Universal

section OddCharacteristic

variable {K : Type u} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {E : Type w} [Group E] [Finite E] {π : E →* K}
  {k : Type*} [Field k] [Finite k]

theorem not_ringChar_dvd_card_ker (hk : ringChar k ≠ 2) (h2 : IsPGroup 2 π.ker) :
    ¬ ringChar k ∣ Nat.card π.ker :=
  not_dvd_card_of_isPGroup_two h2 (CharP.char_is_prime k _) hk

theorem existsUnique_section_of_rankOne_sl2 (hk : ringChar k ≠ 2)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hX : ∀ γ ∈ D.roots, IsPGroup (ringChar k) (D.rootGroup γ))
    (hρ : ∀ i, ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective ρ ∧
      rankOne D.rootGroup i ≤ ρ.range)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃! σ : K →* E, ∀ x, π (σ x) = x := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  refine existsUnique_section_of_rankOne_lift hct hext hX hπ hker
    (not_ringChar_dvd_card_ker hk h2) fun i => ?_
  obtain ⟨ρ, hρi, hL⟩ := hρ i
  obtain ⟨ρ', hρ'⟩ := exists_lift hk hπ hker h2 ρ
  exact exists_lift_of_injective hρi hL fun g => DFunLike.congr_fun hρ' g

theorem existsUnique_section_of_sl2 (hk : ringChar k ≠ 2)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    (hρ : ∀ i, ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective ρ ∧
      (∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c) ∧ ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃! σ : K →* E, ∀ x, π (σ x) = x :=
  existsUnique_section_of_rankOne_sl2 hk hct hext
    (fun _ hγ => isPGroup_of_isParametrization hx hγ)
    (fun i => (hρ i).imp fun _ h => ⟨h.1, rankOne_le_range_of_sl2 hx i h.2.1 h.2.2⟩) hπ hker h2

end OddCharacteristic

end CFSG.LieType.Steinberg
