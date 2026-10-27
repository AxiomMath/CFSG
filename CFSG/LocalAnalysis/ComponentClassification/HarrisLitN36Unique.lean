module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Reduce
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Suz

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts
open scoped commutatorElement Pointwise

section Lift

variable {A B : Type} [Group A] [Group B]

theorem map_subtype_normal' {N : Subgroup A} [N.Normal] (M : Subgroup N) [hM : M.Characteristic] :
    (M.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hfix := hM.fixed (MulAut.conjNormal (H := N) g⁻¹)
  have hk' : (MulAut.conjNormal (H := N) g k) ∈ M := by
    have he : (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom (MulAut.conjNormal (H := N) g k) =
        k := by
      ext
      simp
    have h1 : (MulAut.conjNormal (H := N) g k) ∈
        M.comap (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom := by
      rw [mem_comap, he]
      exact hk
    rwa [hfix] at h1
  exact ⟨_, hk', by simp [MulAut.conjNormal_apply]⟩

theorem commutatorElement_center_mul_left {c x y : A} (hc : c ∈ center A) :
    ⁅c * x, y⁆ = ⁅x, y⁆ := by
  have h := commutatorElement_center_mul (G := A) (x := x) (y := y) hc (one_mem _)
  rwa [one_mul] at h

theorem commutatorElement_mem_pPrimeCore [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ center A) (h2 : IsPGroup 2 f.ker) {x : A} (hx : f x ∈ pPrimeCore 2 B)
    (y : A) : ⁅x, y⁆ ∈ pPrimeCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  set N : Subgroup A := (pPrimeCore 2 B).comap f with hNdef
  have hNn : N.Normal := (pPrimeCore_normal (p := 2) (G := B)).comap f
  have hkN : f.ker ≤ N := fun k hk => by
    rw [hNdef, mem_comap, (MonoidHom.mem_ker).mp hk]
    exact one_mem _
  set S : Subgroup N := f.ker.subgroupOf N with hSdef
  have hSc : S ≤ center N := fun s hs => by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hker hs) g)
  have hSn : S.Normal := normal_of_le_center hSc
  let fN : N →* pPrimeCore 2 B := (f.domRestrict N).codRestrict _ fun n => n.2
  have hfN : Function.Surjective fN := by
    rintro ⟨o, ho⟩
    obtain ⟨a, rfl⟩ := hf o
    exact ⟨⟨a, ho⟩, rfl⟩
  have hkerN : fN.ker = S := by
    ext n
    rw [MonoidHom.mem_ker, hSdef, mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hindex : S.index = Nat.card (pPrimeCore 2 B) := by
    rw [← hkerN, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective fN hfN,
      Subgroup.card_top]
  have hS2 : IsPGroup 2 S := h2.of_equiv (subgroupOfEquivOfLe hkN).symm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS2
  have hcop : Nat.Coprime (Nat.card S) S.index := by
    rw [ha, hindex]
    exact Nat.Coprime.pow_left _ pPrimeCore_coprime_card
  obtain ⟨M, hM⟩ := exists_right_complement'_of_coprime hcop
  have hsup : S ⊔ M = ⊤ := hM.sup_eq_top
  have hMcard : Nat.card M = S.index := by
    have h1 := hM.card_mul_card
    have h3 := Subgroup.card_mul_index S
    have hpos : 0 < Nat.card S := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h3.symm)
  have hdecomp : ∀ g : N, ∃ s ∈ S, ∃ m ∈ M, s * m = g := by
    intro g
    have hg : g ∈ ((S ⊔ M : Subgroup N) : Set N) := by rw [hsup]; exact mem_top g
    rw [normal_mul S M] at hg
    obtain ⟨s, hs, m, hm, hsm⟩ := Set.mem_mul.mp hg
    exact ⟨s, hs, m, hm, hsm⟩
  have hMn : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨s, hs, m', hm', rfl⟩ := hdecomp g
    have hsc := mem_center_iff.mp (hSc hs)
    have e : s * m' * m * (s * m')⁻¹ = m' * m * m'⁻¹ := by
      calc s * m' * m * (s * m')⁻¹ = s * (m' * m * m'⁻¹) * s⁻¹ := by group
        _ = m' * m * m'⁻¹ := by rw [← hsc]; group
    rw [e]
    exact M.mul_mem (M.mul_mem hm' hm) (M.inv_mem hm')
  have hMO : M ≤ pPrimeCore 2 N := by
    refine le_pPrimeCore_of_normal_coprime hMn ?_
    rw [hMcard, hindex]
    exact pPrimeCore_coprime_card
  have hON : ((pPrimeCore 2 N).map N.subtype).Normal := map_subtype_normal' _
  have hONA : (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 A := by
    refine le_pPrimeCore_of_normal_coprime hON ?_
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  obtain ⟨s, hs, m, hm, hsm⟩ := hdecomp ⟨x, hx⟩
  have hx' : x = (s : A) * (m : A) := by
    have h1 := congrArg Subtype.val hsm
    simpa using h1.symm
  have hmO : (m : A) ∈ (pPrimeCore 2 N).map N.subtype := ⟨m, hMO hm, rfl⟩
  have hsZ : (s : A) ∈ center A := hker hs
  rw [hx', commutatorElement_center_mul_left hsZ, commutatorElement_def]
  apply hONA
  have hy : y * (m : A)⁻¹ * y⁻¹ ∈ (pPrimeCore 2 N).map N.subtype :=
    hON.conj_mem _ (inv_mem hmO) y
  have := ((pPrimeCore 2 N).map N.subtype).mul_mem hmO hy
  simpa [mul_assoc] using this

theorem isQuasisimple_quot_of_central_two [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (hker : f.ker ≤ center A) (h2 : IsPGroup 2 f.ker) [Group.IsPerfect A]
    (hB : IsQuasisimple (B ⧸ pPrimeCore 2 B)) : IsQuasisimple (A ⧸ pPrimeCore 2 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  have hOA : (pPrimeCore 2 A).map f ≤ pPrimeCore 2 B :=
    le_pPrimeCore_of_normal_coprime ((pPrimeCore_normal (p := 2) (G := A)).map f hf)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card)
  let h := QuotientGroup.map (pPrimeCore 2 A) (pPrimeCore 2 B) f (map_le_iff_le_comap.mp hOA)
  have hh : Function.Surjective h := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩
  refine GSThmB.Suz24.isQuasisimple_of_surjective h hh hB ?_
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : f x ∈ pPrimeCore 2 B := by
    rw [MonoidHom.mem_ker] at hq
    exact (QuotientGroup.eq_one_iff _).mp hq
  rw [mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  have hc := commutatorElement_mem_pPrimeCore f hf hker h2 hx y
  rw [commutatorElement_def] at hc
  have h1 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : A ⧸ pPrimeCore 2 A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  have h3 : (QuotientGroup.mk (x * y) : A ⧸ pPrimeCore 2 A) =
      QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) * QuotientGroup.mk (y * x) := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    group
  rw [h3, h1, one_mul]

end Lift

variable {G : Type} [Group G]

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem eq_bar_of_isTwoComponentIn [Finite G] (hO : pPrimeCore 2 G = ⊥) {τ : MulAut G}
    {K : Subgroup G} (huniq : ∀ K' : Subgroup G, IsTwoComponentIn K' (fixedPoints τ) → K' = K)
    {J : Subgroup (G ⧸ center G)} (hJ : IsTwoComponentIn J (fixedPoints (quotAut τ))) :
    J = K.map (QuotientGroup.mk' (center G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center G) with hπ
  have hJperf : ⁅J, J⁆ = J := by
    have : Group.IsPerfect ↥J := hJ.2.2.1
    exact Subgroup.commutator_eq_self
  have hJD : J ≤ barFix τ := by
    rw [← hJperf]
    exact (commutator_mono hJ.1 hJ.1).trans (commutator_le_barFix τ)
  set J₀ : Subgroup G := fixedPoints τ ⊓ J.comap π with hJ₀
  have hJ₀map : J₀.map π = J := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro j hj
      obtain ⟨x, hx, rfl⟩ := hJD hj
      exact ⟨x, ⟨hx, hj⟩, rfl⟩
  set J₁ : Subgroup G := ⁅J₀, J₀⁆ with hJ₁
  have hJ₁J₀ : J₁ ≤ J₀ := commutator_self_le J₀
  have hJ₁map : J₁.map π = J := by
    rw [hJ₁, map_commutator, hJ₀map, hJperf]
  have hJ₀le : J₀ ≤ J₁ ⊔ center G := by
    intro x hx
    have hx' : π x ∈ J₁.map π := by rw [hJ₁map, ← hJ₀map]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx'
    have hk : y⁻¹ * x ∈ center G := by
      rw [← QuotientGroup.ker_mk' (center G), MonoidHom.mem_ker, map_mul, map_inv, hyx,
        inv_mul_cancel]
    have := mul_mem_sup hy hk
    rwa [mul_inv_cancel_left] at this
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := by
    apply le_antisymm (commutator_self_le J₁)
    rw [hJ₁]
    refine (commutator_mono hJ₀le hJ₀le).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [← SetLike.mem_coe, mul_normal J₁ (center G)] at ha hb
    obtain ⟨a₁, ha₁, c, hc, rfl⟩ := Set.mem_mul.mp ha
    obtain ⟨b₁, hb₁, d, hd, rfl⟩ := Set.mem_mul.mp hb
    have hca : a₁ * c = c * a₁ := (mem_center_iff.mp hc a₁)
    have hdb : b₁ * d = d * b₁ := (mem_center_iff.mp hd b₁)
    rw [hca, hdb, commutatorElement_center_mul hc hd]
    exact commutator_mem_commutator ha₁ hb₁
  have hJ₁le : J₁ ≤ fixedPoints τ := hJ₁J₀.trans inf_le_left
  have hJ₀sub : (J₀.subgroupOf (fixedPoints τ)).IsSubnormal := by
    have heq : J₀.subgroupOf (fixedPoints τ) = (J.subgroupOf (fixedPoints (quotAut τ))).comap
        (fixHom τ) := by
      ext x
      rw [mem_subgroupOf, mem_comap, mem_subgroupOf, fixHom_apply]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [heq]
    exact hJ.2.1.comap _
  have hJ₁sub : (J₁.subgroupOf (fixedPoints τ)).IsSubnormal := by
    have hle : J₁.subgroupOf (fixedPoints τ) ≤ J₀.subgroupOf (fixedPoints τ) :=
      fun x hx => hJ₁J₀ hx
    refine IsSubnormal.trans hle ?_ hJ₀sub
    refine (Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩)
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    have hg : ((g : ↥(fixedPoints τ)) : G) ∈ J₀ := g.2
    have hnJ₀ : (((n : ↥(fixedPoints τ)) : G)) ∈ J₀ := hJ₁J₀ hn
    have hc : ⁅((g : ↥(fixedPoints τ)) : G), ((n : ↥(fixedPoints τ)) : G)⁆ ∈ J₁ :=
      commutator_mem_commutator hg hnJ₀
    have he : (((g * n * g⁻¹ : ↥(J₀.subgroupOf (fixedPoints τ))) : ↥(fixedPoints τ)) : G) =
        ⁅((g : ↥(fixedPoints τ)) : G), ((n : ↥(fixedPoints τ)) : G)⁆ *
          ((n : ↥(fixedPoints τ)) : G) := by
      simp [commutatorElement_def]
    rw [he]
    exact J₁.mul_mem hc hn
  have hJ₁perf' : Group.IsPerfect ↥J₁ := Subgroup.isPerfect_iff.mpr hJ₁perf
  let g : ↥J₁ →* ↥J := (π.domRestrict J₁).codRestrict J fun x => by
    rw [← hJ₁map]
    exact ⟨x, x.2, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨j, hj⟩
    rw [← hJ₁map] at hj
    obtain ⟨x, hx, rfl⟩ := hj
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgker : ∀ k : ↥J₁, k ∈ g.ker ↔ (k : G) ∈ center G := by
    intro k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : π (k : G) = 1 := congrArg Subtype.val h
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hker : g.ker ≤ center ↥J₁ := fun k hk => by
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (mem_center_iff.mp ((hgker k).mp hk) w)
  have h2 : IsPGroup 2 g.ker := by
    intro k
    obtain ⟨n, hn⟩ := center_isPGroup hO ⟨(k : ↥J₁), (hgker k).mp k.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hJ₁q := isQuasisimple_quot_of_central_two g hg hker h2 hJ.2.2.2
  have hJ₁c : IsTwoComponentIn J₁ (fixedPoints τ) := ⟨hJ₁le, hJ₁sub, hJ₁perf', hJ₁q⟩
  rw [← hJ₁map, huniq J₁ hJ₁c]

end CFSG.ComponentClassification.HarrisLit.N36
