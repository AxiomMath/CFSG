module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.Sp4.Defs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open CFSG.Open

section Lift

variable {q : ℕ} [Fact q.Prime]

private noncomputable def spConj (q : ℕ) [Fact q.Prime] :
    StatedSp 2 (ZMod q) →* MulAut (StatedProj (StatedSp 2 (ZMod q))) :=
  MulAut.conj.comp (QuotientGroup.mk' _)

private theorem spConj_apply (g : StatedSp 2 (ZMod q)) :
    spConj q g = MulAut.conj (QuotientGroup.mk g : StatedProj (StatedSp 2 (ZMod q))) := rfl

private theorem center_statedProj_eq_bot (hq2 : q ≠ 2) :
    Subgroup.center (StatedProj (StatedSp 2 (ZMod q))) = ⊥ := by
  have hcard : Nat.card (ZMod q) = q := Nat.card_zmod q
  have hq3 : 3 ≤ q := by have := (Fact.out : q.Prime).two_le; omega
  have hQ := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 (ZMod q) (by norm_num) (by
    rcases eq_or_lt_of_le hq3 with h | h
    · exact Or.inr (Or.inl ⟨by rw [hcard, h], le_rfl⟩)
    · exact Or.inl (Or.inr (by rw [hcard]; omega)))
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  let e := CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 (ZMod q)
  have : IsSimpleGroup (StatedProj (StatedSp 2 (ZMod q))) := e.symm.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp 2 (ZMod q)))) with h | h
  · exact h
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (e a)) (e b)).symm

private theorem mem_scalars_of_spConj_eq_one (hq2 : q ≠ 2) {g : StatedSp 2 (ZMod q)}
    (hg : spConj q g = 1) :
    g ∈ (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod q)).subgroupOf (StatedSp 2 (ZMod q)) := by
  have hc : (QuotientGroup.mk g : StatedProj (StatedSp 2 (ZMod q))) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := congrArg (fun f : MulAut _ => f z) hg
    simp only [spConj_apply, MulAut.conj_apply, MulAut.one_apply] at h
    exact ((mul_inv_eq_iff_eq_mul.mp h)).symm
  rw [center_statedProj_eq_bot hq2, Subgroup.mem_bot] at hc
  exact (QuotientGroup.eq_one_iff g).mp hc

private theorem sq_eq_one_of_mem_scalars {g : StatedSp 2 (ZMod q)}
    (hg : g ∈ (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod q)).subgroupOf (StatedSp 2 (ZMod q))) :
    g ^ 2 = 1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars] at hg
  obtain ⟨c, hc⟩ := hg
  have hg2 : (g : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ TauCeti.GLSymplectic (Fin 2) (ZMod q) :=
    CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := ZMod q) ▸ g.2
  have hmem := TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hg2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hmem
  have h2 : (c : ZMod q) ^ 2 = 1 :=
    (CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff (by norm_num) _).mp hmem
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar,
    Subgroup.coe_one, Units.val_one, ← map_pow, h2, map_one]

private theorem eq_one_of_spConj_eq_one (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g : StatedSp 2 (ZMod q)} (hg : spConj q g = 1) {k : ℕ} (hk : g ^ p ^ k = 1) : g = 1 := by
  have h2 := sq_eq_one_of_mem_scalars (mem_scalars_of_spConj_eq_one hq2 hg)
  have hcop : Nat.Coprime 2 (p ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [← orderOf_eq_one_iff]
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hk)
  rwa [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h

private theorem exists_section (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (StatedProj (StatedSp 2 (ZMod q))))) (hc : Nat.card E = p ^ 2)
    (hinn : E ≤ (MulAut.conj : StatedProj (StatedSp 2 (ZMod q)) →* MulAut _).range) :
    ∃ Q : Subgroup (StatedSp 2 (ZMod q)), (∀ y ∈ Q, spConj q y ∈ E) ∧
      (∀ y ∈ Q, spConj q y = 1 → y = 1) ∧ ∀ α ∈ E, ∃ y ∈ Q, spConj q y = α := by
  have : Fact p.Prime := ⟨hp⟩
  set P := E.comap (spConj q)
  have hψ : Function.Surjective ((spConj q).subgroupComap E) := by
    rintro ⟨α, hα⟩
    obtain ⟨s, rfl⟩ := hinn hα
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨⟨g, hα⟩, rfl⟩
  obtain ⟨Q₀⟩ := (Sylow.nonempty : Nonempty (Sylow p P))
  have htop : ((Q₀.mapSurjective hψ : Sylow p E) : Subgroup E) = ⊤ :=
    ((Q₀.mapSurjective hψ).is_maximal' ((IsPGroup.of_card hc).to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(Q₀ : Subgroup P).map P.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · rintro _ ⟨w, hw, rfl⟩ h1
    obtain ⟨k, hk⟩ := Q₀.isPGroup' ⟨w, hw⟩
    refine eq_one_of_spConj_eq_one hq2 hp hp2 h1 (k := k) ?_
    have := congrArg (fun x : Q₀ => ((x : P) : StatedSp 2 (ZMod q))) hk
    simpa using this
  · intro α hα
    obtain ⟨w, hw, hwα⟩ := (htop ▸ Subgroup.mem_top (⟨α, hα⟩ : E) :
      (⟨α, hα⟩ : E) ∈ (Q₀ : Subgroup P).map ((spConj q).subgroupComap E))
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwα⟩

theorem exists_isElemSp_of_le_range_conj {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)))))
    (hE : CFSG.Open.IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinn : E ≤ (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 (ZMod q)) →*
      MulAut _).range) :
    ∃ Ê : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)), IsElemSp p Ê ∧
      ∀ g ∈ Ê, g ≠ 1 → ∃ α ∈ E, α ≠ 1 ∧ ∀ x : CFSG.Open.StatedSp 2 (ZMod q),
        g * (x : GL (Fin 2 ⊕ Fin 2) (ZMod q)) = x * g →
          α (QuotientGroup.mk x) = QuotientGroup.mk x := by
  obtain ⟨Q, hQE, hQ1, hQsurj⟩ := exists_section hq2 hp hp2 E hc hinn
  have hinj : ∀ y ∈ Q, ∀ z ∈ Q, spConj q y = spConj q z → y = z := by
    intro y hy z hz h
    rw [← mul_inv_eq_one]
    exact hQ1 _ (Q.mul_mem hy (Q.inv_mem hz)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  let f : Q → E := fun y => ⟨spConj q y, hQE y y.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun y z h => Subtype.ext (hinj y y.2 z z.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨α, hα⟩
    obtain ⟨y, hy, rfl⟩ := hQsurj α hα
    exact ⟨⟨y, hy⟩, rfl⟩
  refine ⟨Q.map (StatedSp 2 (ZMod q)).subtype, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hinj _ (Q.mul_mem hy hz) _ (Q.mul_mem hz hy) ?_]
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hQE y hy⟩ : E) ⟨_, hQE z hz⟩)
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hQ1 _ (Q.pow_mem hy p) (by rw [map_pow]; exact hE.2 _ (hQE y hy)), map_one]
  · rw [Subgroup.card_map_of_injective Subtype.val_injective,
      Nat.card_congr (Equiv.ofBijective f hf), hc]
  · rintro _ ⟨y, hy, rfl⟩ hy1
    refine ⟨spConj q y, hQE y hy, fun h => hy1 ?_, ?_⟩
    · rw [hQ1 y hy h, map_one]
    · intro x hx
      have hyx : y * x = x * y := Subtype.ext hx
      rw [spConj_apply, MulAut.conj_apply, ← QuotientGroup.mk_mul, hyx, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, mul_inv_cancel_right]

end Lift

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
