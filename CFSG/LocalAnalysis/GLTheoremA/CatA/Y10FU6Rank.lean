module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FU6Center
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U5Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Snoc

@[expose] def snocInv {A : Type} [CommGroup A] (m : ℕ) : (Fin m → A) →* (Fin (m + 1) → A) where
  toFun v := Fin.snoc (α := fun _ => A) v (∏ i, v i)⁻¹
  map_one' := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.one_apply, Finset.prod_const_one, inv_one]
    · simp only [Fin.snoc_castSucc, Pi.one_apply]
  map_mul' x y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
    · simp only [Fin.snoc_castSucc, Pi.mul_apply]

theorem snocInv_castSucc {A : Type} [CommGroup A] (m : ℕ) (v : Fin m → A) (i : Fin m) :
    snocInv m v i.castSucc = v i :=
  Fin.snoc_castSucc (α := fun _ => A) _ _ _

theorem snocInv_last {A : Type} [CommGroup A] (m : ℕ) (v : Fin m → A) :
    snocInv m v (Fin.last m) = (∏ i, v i)⁻¹ :=
  Fin.snoc_last (α := fun _ => A) _ _

theorem prod_snocInv {A : Type} [CommGroup A] (m : ℕ) (v : Fin m → A) : ∏ j, snocInv m v j = 1 := by
  rw [Fin.prod_univ_castSucc]
  simp only [snocInv_castSucc, snocInv_last]
  exact mul_inv_cancel _

end Snoc

section Rank


theorem exists_elemAbelian_five_projSU_six {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 4) :
    ∃ E : Subgroup (StatedProj (StatedSU 6 (2 ^ 2) F)), IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 5 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h16 : Fintype.card F = 2 ^ 4 := by rw [← Nat.card_eq_fintype_card, hF]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5card : 5 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units, h16]
    norm_num
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 5 h5card
  have h5 : ζ ^ 5 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  let τ : (Fin 5 → Multiplicative (ZMod 5)) →* StatedSU 6 (2 ^ 2) F :=
    { toFun := fun v => ⟨u5Torus ζ h5 (snocInv 5 v), u5Torus_mem ζ h5 _ (by
        rw [← map_prod]
        exact (congrArg (u5Chi ζ h5) (prod_snocInv 5 v)).trans (map_one _))⟩
      map_one' := Subtype.ext (by
        show u5Torus ζ h5 (snocInv 5 1) = 1
        rw [map_one, map_one])
      map_mul' := fun v w => Subtype.ext (by
        show u5Torus ζ h5 (snocInv 5 (v * w)) = u5Torus ζ h5 (snocInv 5 v) * u5Torus ζ h5 (snocInv 5 w)
        rw [map_mul, map_mul]) }
  let ψ : (Fin 5 → Multiplicative (ZMod 5)) →* StatedProj (StatedSU 6 (2 ^ 2) F) :=
    (QuotientGroup.mk' _).comp τ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    change (QuotientGroup.mk (τ v) : StatedProj (StatedSU 6 (2 ^ 2) F)) = 1 at hv
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (show (τ v : GL (Fin 6) F) ∈
      (StatedScalars (Fin 6) F) from hv)
    have hall : ∀ i, u5Chi ζ h5 (snocInv 5 v i) = c := fun i =>
      u5Torus_entry ζ h5 _ c hc.symm i
    have hc5 : c ^ 5 = 1 := by
      have h0 := hall 0
      rw [← h0, ← map_pow, u5_pow5_chi, map_one]
    have hc6 : c ^ 6 = 1 := by
      have hprod : ∏ i, u5Chi ζ h5 (snocInv 5 v i) = 1 := by
        rw [← map_prod]
        exact (congrArg (u5Chi ζ h5) (prod_snocInv 5 v)).trans (map_one _)
      simpa [hall] using hprod
    have hc1 : c = 1 := by
      have : c = c ^ 6 * (c ^ 5)⁻¹ := by group
      rw [this, hc6, hc5]; simp
    have hv1 : ∀ i : Fin 5, v i = 1 := fun i => by
      have := hall i.castSucc
      rw [snocInv_castSucc, hc1] at this
      exact (u5Chi_eq_one ζ h5 hζ _).1 this
    exact funext hv1
  refine ⟨ψ.range, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 5 = 1 := by
      funext i
      exact u5_pow5_chi (x i)
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv]
    simp [Nat.card_pi]

theorem u6Rank_holds : U6Rank := by
  intro L _ _ hL
  have hcen := u6Center_holds L hL
  obtain ⟨hn1, hQ, hM⟩ := hasLabel_model hL
  have hLM : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 6 2 2 :=
    i61_model_psu hM (lab := ⟨.twA, 5, 2⟩) rfl rfl
  have hsc : CFSG.Open.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 6 2 2 := by
    rcases hLM with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  obtain ⟨-, F, hFi, hFf, hF, ⟨e⟩⟩ := hsc
  have hF16 : Nat.card F = 2 ^ 4 := by rw [hF]; norm_num
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_five_projSU_six hF16
  let φ : L →* StatedProj (StatedSU 6 (2 ^ 2) F) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext z
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    rw [show φ z = e (QuotientGroup.mk z) from rfl, map_eq_one_iff e (MulEquiv.injective e),
      QuotientGroup.eq_one_iff, hcen]
    simp
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) x
    exact ⟨z, rfl⟩
  refine ⟨E.comap φ, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hφinj
    have ha : φ a ∈ E := a.2
    have hb : φ b ∈ E := b.2
    have := isElemAbelian_commute hE ha hb
    simpa using this
  · apply hφinj
    have := hE.2 (φ x) hx
    rw [map_pow, this, map_one]
  · rw [← hcard, ← Subgroup.card_map_of_injective hφinj,
      Subgroup.map_comap_eq_self_of_surjective hφsurj]

theorem u6StructAt_of_facts (hm : U6Mem) (ht : U6Cent) {G : Type} [Group G] [Finite G] :
    U6StructAt G :=
  u6StructAt_of_four_facts u6Center_holds u6Rank_holds hm ht

end Rank

end CFSG.LocalAnalysis.GLTheoremA.Y10F
