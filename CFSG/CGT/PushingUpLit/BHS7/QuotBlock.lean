module

public import CFSG.CGT.PushingUpLit.BHS7.QuotOffender
public import CFSG.CGT.PushingUpLit.BHS7.TwoSixteenDich

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.RankThree.PartOne
  CFSG.LieType.BorelTits CFSG.QuasithinUnique.Setup.Campbell CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5
open scoped commutatorElement

theorem natSection_transfer_down {V V' H K : Type*} [CommGroup V] [CommGroup V'] [Group K] [Mul H]
    (act : H → K → K) {X : Subgroup (MulAut V)} {W Z : Subgroup V} {X' : Subgroup (MulAut V')}
    {W' Z' : Subgroup V'} (ι : ↥X ≃* ↥X') (π : ↥W →* ↥W') (hπ : Function.Surjective π)
    (hker : ∀ p : ↥W, π p ∈ Z'.subgroupOf W' ↔ p ∈ Z.subgroupOf W)
    (hstab : ∀ (x : ↥X) (p : ↥W), (x : MulAut V) p ∈ W)
    (hequiv : ∀ (x : ↥X) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
      ((π ⟨(x : MulAut V) p, hp⟩ : ↥W') : V') = ((ι x : ↥X') : MulAut V') ((π p : ↥W') : V'))
    (h : ∃ (θ : ↥X ≃* H) (β : ↥W →* K), Function.Surjective β ∧ β.ker = Z.subgroupOf W ∧
      ∀ (x : ↥X) (p : ↥W) (hp : (x : MulAut V) p ∈ W),
        β ⟨(x : MulAut V) p, hp⟩ = act (θ x) (β p)) :
    ∃ (θ : ↥X' ≃* H) (β : ↥W' →* K), Function.Surjective β ∧ β.ker = Z'.subgroupOf W' ∧
      ∀ (x : ↥X') (p : ↥W') (hp : (x : MulAut V') p ∈ W'),
        β ⟨(x : MulAut V') p, hp⟩ = act (θ x) (β p) := by
  obtain ⟨θ, β, hsurj, hkerβ, hβ⟩ := h
  have hle : π.ker ≤ β.ker := by
    intro p hp
    rw [hkerβ, ← hker]
    rw [MonoidHom.mem_ker] at hp
    rw [hp]
    exact one_mem _
  let β' : ↥W' →* K :=
    MonoidHom.liftOfRightInverse π (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
      ⟨β, hle⟩
  have hβ' : ∀ p : ↥W, β' (π p) = β p := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply π _ _ ⟨β, hle⟩ p
  refine ⟨ι.symm.trans θ, β', ?_, ?_, ?_⟩
  · intro k
    obtain ⟨p, rfl⟩ := hsurj k
    exact ⟨π p, hβ' p⟩
  · ext y
    obtain ⟨p, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hβ', ← MonoidHom.mem_ker, hkerβ, hker]
  · intro x' p' hp'
    obtain ⟨p, rfl⟩ := hπ p'
    have hxp : ((ι.symm x' : ↥X) : MulAut V) p ∈ W := hstab _ p
    have hix : ι (ι.symm x') = x' := ι.apply_symm_apply x'
    have h1 : π ⟨((ι.symm x' : ↥X) : MulAut V) p, hxp⟩ = ⟨(x' : MulAut V') (π p), hp'⟩ :=
      Subtype.ext (by rw [hequiv _ p hxp, hix])
    show β' ⟨(x' : MulAut V') (π p), hp'⟩ = act (θ (ι.symm x')) (β' (π p))
    rw [← h1, hβ', hβ _ p hxp, hβ']

section Aut

variable {V : Type} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)}

omit [Finite V] in
theorem isSLNatSection_qImg (hV : ∀ v : V, v ^ 2 = 1) (hinj : Function.Injective (BHS5.quotHom K))
    {n : ℕ} {E : Subgroup (MulAut V)} (hEK : E ≤ K)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)})
    (h : IsSLNatSection E (commV E) (commV E ⊓ fixV E) n) :
    IsSLNatSection (qImg K E) (commV (qImg K E)) (commV (qImg K E) ⊓ fixV (qImg K E)) n :=
  ⟨fun _ hx _ hp => map_mem_commV_of_mem hx hp,
    natSection_transfer_down (fun (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (v : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd v)))
      (quotImgEquiv hinj hEK) (commVQuot hEK) (commVQuot_surjective hEK)
      (commVQuot_mem_iff hV hEK hEgen) (fun x p => map_mem_commV_of_mem x.2 p.2)
      (fun _ _ _ => rfl) h.2⟩

omit [Finite V] in
theorem isAltNatSection_qImg (hV : ∀ v : V, v ^ 2 = 1) (hinj : Function.Injective (BHS5.quotHom K))
    {m : ℕ} {E : Subgroup (MulAut V)} (hEK : E ≤ K)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)})
    (h : IsAltNatSection E (commV E) (commV E ⊓ fixV E) m) :
    IsAltNatSection (qImg K E) (commV (qImg K E)) (commV (qImg K E) ⊓ fixV (qImg K E)) m :=
  ⟨fun _ hx _ hp => map_mem_commV_of_mem hx hp,
    natSection_transfer_down (fun (σ : alternatingGroup (Fin m)) (v : ↥(coreMod m)) =>
        coreAct m (σ : Equiv.Perm (Fin m)) v)
      (quotImgEquiv hinj hEK) (commVQuot hEK) (commVQuot_surjective hEK)
      (commVQuot_mem_iff hV hEK hEgen) (fun x p => map_mem_commV_of_mem x.2 p.2)
      (fun _ _ _ => rfl) h.2⟩

omit [Finite V] in
theorem eq_one_of_fix_commV {E : Subgroup (MulAut V)}
    (htype : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection E (commV E) (commV E ⊓ fixV E) (2 * m + 1))
    {x : MulAut V} (hx : x ∈ E) (hfix : ∀ w ∈ commV E, x w = w) : x = 1 := by
  rcases htype with ⟨k, hk, -, θ, β, hβs, hβk, hβe⟩ | ⟨m, hm, -, θ, β, hβs, hβk, hβe⟩
  · have h1 : θ ⟨x, hx⟩ = 1 := by
      apply eq_one_of_forall_smul_vec
      intro v
      obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd v)
      have hpW : x (p : V) ∈ commV E := by rw [hfix p p.2]; exact p.2
      have hp' : (⟨x p, hpW⟩ : ↥(commV E)) = p := Subtype.ext (hfix p p.2)
      have := hβe ⟨x, hx⟩ p hpW
      rw [hp', hp] at this
      have h2 := congrArg Multiplicative.toAdd this
      have h3 : (θ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec v = v := by
        simpa only [toAdd_ofAdd] using h2.symm
      exact h3
    have : (⟨x, hx⟩ : ↥E) = 1 := θ.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · have hn3 : 3 ≤ 2 * m + 1 := by omega
    have h1 : ((θ ⟨x, hx⟩ : alternatingGroup (Fin (2 * m + 1))) :
        Equiv.Perm (Fin (2 * m + 1))) = 1 := by
      apply coreAct_injective hn3
      rw [map_one]
      refine MulEquiv.ext fun v => ?_
      obtain ⟨p, hp⟩ := hβs v
      have hpW : x (p : V) ∈ commV E := by rw [hfix p p.2]; exact p.2
      have hp' : (⟨x p, hpW⟩ : ↥(commV E)) = p := Subtype.ext (hfix p p.2)
      have := hβe ⟨x, hx⟩ p hpW
      rw [hp', hp] at this
      rw [MulAut.one_apply]
      exact this.symm
    have h2 : θ ⟨x, hx⟩ = 1 := Subtype.ext h1
    have : (⟨x, hx⟩ : ↥E) = 1 := θ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val this

end Aut

section Finite

variable {V : Type} [CommGroup V] [Finite V]

theorem commutator_eq_bot_of_minimal (hV : ∀ v : V, v ^ 2 = 1) {H E A : Subgroup (MulAut V)}
    (hAH : A ≤ H) (hEH : E ≤ H) (hsub : IsSubnormal E H)
    (htype : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection E (commV E) (commV E ⊓ fixV E) (2 * m + 1))
    (hA : IsOffStar A) (hmin : ∀ B : Subgroup (MulAut V), B ≤ A → IsOffStar B → B = A) :
    ⁅E, A⁆ = ⊥ := by
  rcases two_sixteen_dich hV hA.1 hAH hEH hsub htype with h | ⟨hAN, hrel⟩
  · exact h
  · rcases offender_card_lt_or hA (commV E) with hlt | hstar
    · exact absurd hrel (ne_of_lt hlt)
    · have hAeq : cenIn A (commV E) = A := hmin _ (cenIn_le A _) hstar
      have hfix : ∀ a ∈ A, ∀ w ∈ commV E, a w = w := fun a ha w hw => by
        have hmem : a ∈ cenIn A (commV E) := by rw [hAeq]; exact ha
        exact (mem_cenIn.mp hmem).2 w hw
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro e he a ha
      rw [Subgroup.mem_bot]
      have hN : a * e * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hAN ha) e).mp he
      have hx : (a * e * a⁻¹) * e⁻¹ ∈ E := E.mul_mem hN (E.inv_mem he)
      have hx1 : (a * e * a⁻¹) * e⁻¹ = 1 := by
        refine eq_one_of_fix_commV htype hx fun w hw => ?_
        have hew : e⁻¹ w ∈ commV E := map_mem_commV_of_mem (E.inv_mem he) hw
        have h1 : a⁻¹ (e⁻¹ w) = e⁻¹ w := hfix a⁻¹ (A.inv_mem ha) _ hew
        have h2 : a w = w := hfix a ha w hw
        simp only [MulAut.mul_apply, h1]
        simpa using h2
      have hc : ⁅a, e⁆ = 1 := hx1
      rw [← inv_inv ⁅e, a⁆, commutatorElement_inv, hc, inv_one]

end Finite

section QAut

variable {V : Type} [CommGroup V] [Finite V] {K S : Subgroup (MulAut V)}

theorem commutator_eq_bot_of_mem_offQMin (hV : ∀ v : V, v ^ 2 = 1)
    (hinj : Function.Injective (BHS5.quotHom K)) {H E B : Subgroup (MulAut V)} (hSK : S ≤ K)
    (hHK : H ≤ K) (hEH : E ≤ H) (hsub : IsSubnormal E H)
    (hEgen : E ≤ Subgroup.closure {x | x ∈ E ∧ Odd (orderOf x)})
    (htype : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection E (commV E) (commV E ⊓ fixV E) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection E (commV E) (commV E ⊓ fixV E) (2 * m + 1))
    (hBH : B ≤ H) (hB : B ∈ offQMin K S) : ⁅E, B⁆ = ⊥ := by
  have hEK : E ≤ K := hEH.trans hHK
  have hBK : B ≤ K := hB.1.1.trans hSK
  have htype' : (∃ k : ℕ, 2 ≤ k ∧ IsSLNatSection (qImg K E) (commV (qImg K E))
        (commV (qImg K E) ⊓ fixV (qImg K E)) k) ∨
      ∃ m : ℕ, 1 ≤ m ∧ IsAltNatSection (qImg K E) (commV (qImg K E))
        (commV (qImg K E) ⊓ fixV (qImg K E)) (2 * m + 1) := by
    rcases htype with ⟨k, hk, h⟩ | ⟨m, hm, h⟩
    · exact Or.inl ⟨k, hk, isSLNatSection_qImg hV hinj hEK hEgen h⟩
    · exact Or.inr ⟨m, hm, isAltNatSection_qImg hV hinj hEK hEgen h⟩
  have hsub' : IsSubnormal (qImg K E) (qImg K H) :=
    Quasithin.A3.subnormal_map (BHS5.quotHom K) (Quasithin.A3.subnormal_comap K.subtype hsub)
  have hres : ⁅qImg K E, qImg K B⁆ = ⊥ :=
    commutator_eq_bot_of_minimal (BHS5.quot_sq_eq_one hV (fixOp K)) (qImg_mono hBH)
      (qImg_mono hEH) hsub' htype' hB.1.2
      (fun C' hC'B hC' => eq_of_le_qImg hinj hSK hB hC'B hC')
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro e he b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have heK : e ∈ K := hEK he
  have hbK : b ∈ K := hBK hb
  have h1 := Subgroup.commutator_le.mp (le_of_eq hres) (BHS5.quotHom K ⟨e, heK⟩)
    (mem_qImg.2 ⟨⟨e, heK⟩, he, rfl⟩) (BHS5.quotHom K ⟨b, hbK⟩) (mem_qImg.2 ⟨⟨b, hbK⟩, hb, rfl⟩)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (hinj h1)

end QAut

end CFSG.CGT.PushingUpLit.BHS7
