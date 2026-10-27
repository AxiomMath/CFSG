module

public import CFSG.Quasithin.Background.A1cModuleAut
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.Quasithin

theorem exists_pow_eq_of_irreducible {P : Type} [CommGroup P] [Finite P] {σx σy : MulAut P}
    {p : ℕ} (hxo : orderOf σx = p) (hyp : σy ^ p = 1) (hcomm : σx * σy = σy * σx)
    (hirr : ∀ J : Subgroup P, (∀ a ∈ J, σx a ∈ J) → J = ⊥ ∨ J = ⊤) [Nontrivial P] :
    ∃ m : ℕ, σy = σx ^ m := by
  classical
  let A : Subgroup (MulAut P) := Subgroup.zpowers σx
  have hsimple : XMod.IsIrrSec ↥A (⊥ : Subgroup P) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => hirr J fun a ha => ?_⟩
    · obtain ⟨u, hu⟩ := exists_ne (1 : P)
      exact IsConcreteLE.lt_iff_le_and_exists.2
        ⟨bot_le, u, trivial, fun h => hu (Subgroup.mem_bot.1 h)⟩
    · have := hJ ⟨σx, Subgroup.mem_zpowers σx⟩ a ha
      simpa [Subgroup.smul_def] using this
  let Γ : Subgroup (MulAut P) := Subgroup.closure ({σx, σy} : Set (MulAut P))
  have hΓσ : ∀ γ ∈ Γ, γ * σx = σx * γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · rfl
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcomm.symm
    | one => simp
    | mul a b _ _ ha hb =>
      calc a * b * σx = a * (b * σx) := by rw [mul_assoc]
        _ = a * (σx * b) := by rw [hb]
        _ = (a * σx) * b := by rw [mul_assoc]
        _ = (σx * a) * b := by rw [ha]
        _ = σx * (a * b) := by rw [mul_assoc]
    | inv a _ ha => exact (show Commute a σx from ha).inv_left.eq
  have hΓeqv : ∀ γ ∈ Γ, ∀ (a : ↥A) (q : P), γ (a • q) = a • γ q := by
    intro γ hγ a q
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have hc : Commute γ (σx ^ k) := (show Commute γ σx from hΓσ γ hγ).zpow_right k
    have h1 : γ ((σx ^ k) q) = (σx ^ k) (γ q) := congrArg (fun t : MulAut P => t q) hc.eq
    simpa [Subgroup.smul_def, ← hk] using h1
  let f : ↥Γ →* ↥(XMod.eqvEnd ↥A P) :=
    { toFun := fun γ => ⟨MonoidHom.toAdditive (γ.1 : MulAut P).toMonoidHom,
        XMod.mem_eqvEnd_iff.2 (by
          intro a q
          rw [XMod.toMonoidEnd_toAdditive]
          exact hΓeqv γ.1 γ.2 a q)⟩
      map_one' := Subtype.ext (AddMonoidHom.ext fun _ => rfl)
      map_mul' := fun _ _ => Subtype.ext (AddMonoidHom.ext fun _ => rfl) }
  have hf : Function.Injective f := by
    intro γ γ' h
    apply Subtype.ext
    apply MulEquiv.ext
    intro q
    have := congrArg (fun e : ↥(XMod.eqvEnd ↥A P) =>
      (e : AddMonoid.End (Additive P)) (Additive.ofMul q)) h
    exact Additive.ofMul.injective this
  have hcyc : IsCyclic ↥Γ := XMod.isCyclic_of_injective_eqvEnd hsimple f hf
  have hσxΓ : σx ∈ Γ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hσyΓ : σy ∈ Γ := Subgroup.subset_closure (by simp)
  have hcom : ∀ a b : ↥Γ, a * b = b * a := fun a b =>
    (IsCyclic.commGroup : CommGroup ↥Γ).mul_comm a b
  have hexp : ∀ γ : ↥Γ, γ ^ p = 1 := by
    rintro ⟨γ, hγ⟩
    induction hγ using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | hz
      · exact Subtype.ext (hxo ▸ pow_orderOf_eq_one z)
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact Subtype.ext hyp
    | one => simp
    | mul a b ha hb iha ihb =>
      have := Commute.mul_pow (hcom (⟨a, ha⟩ : ↥Γ) ⟨b, hb⟩) p
      rw [iha, ihb, one_mul] at this
      exact this
    | inv a ha iha =>
      have := inv_pow (⟨a, ha⟩ : ↥Γ) p
      rw [iha, inv_one] at this
      exact this
  have hdvd : Monoid.exponent ↥Γ ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rw [IsCyclic.exponent_eq_card] at hdvd
  have hox : orderOf (⟨σx, hσxΓ⟩ : ↥Γ) = p := by
    rw [← hxo, ← Subgroup.orderOf_coe]
  have hcard : Nat.card ↥Γ = p :=
    Nat.dvd_antisymm hdvd (hox ▸ orderOf_dvd_natCard _)
  have htop : Subgroup.zpowers (⟨σx, hσxΓ⟩ : ↥Γ) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hox, hcard]
  have hmem : (⟨σy, hσyΓ⟩ : ↥Γ) ∈ Subgroup.zpowers (⟨σx, hσxΓ⟩ : ↥Γ) := by
    rw [htop]
    trivial
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, (congrArg Subtype.val hm).symm⟩

end CFSG.CGT.PushingUpLit
