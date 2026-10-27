module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnStr

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.LieType.Seitz

theorem eq_of_relIndex_prime {G : Type*} [Group G] {X₀ N X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (h₀N : X₀ ≤ N) (hNX : N ≤ X) (hidx : X₀.relIndex X = p)
    (hy : ∃ y ∈ N, y ∉ X₀) : N = X := by
  have hmul : X₀.relIndex N * N.relIndex X = p := by
    rw [← hidx]
    exact Subgroup.relIndex_mul_relIndex X₀ N X h₀N hNX
  have hdvd : N.relIndex X ∣ p := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exact le_antisymm hNX (Subgroup.relIndex_eq_one.1 h1)
  · exfalso
    rw [h1] at hmul
    have h2 : X₀.relIndex N = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul p).symm)
    obtain ⟨y, hyN, hyX₀⟩ := hy
    exact hyX₀ (Subgroup.relIndex_eq_one.1 h2 hyN)

theorem lineGen_of_index_prime {X : Type} [Group X] {E : Subgroup (MulAut X)} {f : MulAut X}
    {X₀ : Subgroup X} {p : ℕ} (hp : p.Prime)
    (hX₀ : X₀ ≤ fixedPoints (Subgroup.zpowers f))
    (hidx : X₀.relIndex (fixedPoints (Subgroup.zpowers f)) = p)
    (hN₀ : X₀ ≤ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F)
    (hy : ∃ y ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F,
        y ∉ X₀) :
    fixedPoints (Subgroup.zpowers f) ≤
      sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
        ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F := by
  have hNX : sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} ⊔
      ⨆ (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F ≤
        fixedPoints (Subgroup.zpowers f) := by
    refine sup_le (sSup_le fun J hJ => hJ.1) (iSup₂_le fun F hF => ?_)
    intro x hx φ hφ
    exact hx φ (Subgroup.zpowers_le.2 hF.2.2 hφ)
  exact (eq_of_relIndex_prime hp hN₀ hNX hidx hy).ge

theorem noPlane3_of_equiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : NoPlane3 Q) : NoPlane3 Q' := by
  intro D hD hcard
  let φ : MulAut Q' ≃* MulAut Q := (MulAut.congr e).symm
  apply h (D.map φ.toMonoidHom) (CFSG.Open.IsElemAbelian.map hD φ.toMonoidHom)
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hcard

theorem twE6ComponentType_map_injective_iff {X Y : Type} [Group X] [Group Y] (ι : X →* Y)
    (hι : Function.Injective ι) (J : Subgroup X) :
    TwE6ComponentType (J.map ι) ↔ TwE6ComponentType J := by
  let φ : J ≃* J.map ι := J.equivMapOfInjective ι hι
  have hZ : (Subgroup.center J).map φ.toMonoidHom = Subgroup.center (J.map ι) :=
    Subgroup.map_center_eq φ
  let ψ : (J ⧸ Subgroup.center J) ≃* ((J.map ι) ⧸ Subgroup.center (J.map ι)) :=
    QuotientGroup.congr _ _ φ hZ
  have hcZ : Nat.card (Subgroup.center (J.map ι)) = Nat.card (Subgroup.center J) := by
    rw [← hZ]
    exact Subgroup.card_map_of_injective φ.injective
  have hcJ : Nat.card (J.map ι) = Nat.card J := Nat.card_congr φ.toEquiv.symm
  unfold TwE6ComponentType
  rw [hcZ, hcJ]
  constructor
  · rintro (⟨h3, d, e, hd, hex⟩ | hno | hcop)
    · exact Or.inl ⟨h3, d, ψ.trans e, hd, hex⟩
    · exact Or.inr (Or.inl (noPlane3_of_equiv ψ.symm hno))
    · exact Or.inr (Or.inr hcop)
  · rintro (⟨h3, d, e, hd, hex⟩ | hno | hcop)
    · exact Or.inl ⟨h3, d, ψ.symm.trans e, hd, hex⟩
    · exact Or.inr (Or.inl (noPlane3_of_equiv ψ hno))
    · exact Or.inr (Or.inr hcop)

theorem twE6ComponentType_of_map_injective {X Y : Type} [Group X] [Group Y] (ι : X →* Y)
    (hι : Function.Injective ι) {J : Subgroup X} (h : TwE6ComponentType (J.map ι)) :
    TwE6ComponentType J :=
  (twE6ComponentType_map_injective_iff ι hι J).1 h

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
