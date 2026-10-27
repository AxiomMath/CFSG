module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256e2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

section Defs

variable {S : Type} [Group S]

@[expose] def IsChevSubOrCoprime (q p : ℕ) (β : MulAut S) (J : Subgroup S) : Prop :=
  Inputs256e.IsChevSub q β J ∨ (IsSubnormal J (fixSubgroup β) ∧ Nat.Coprime (Nat.card J) p)

@[expose] def QGenCoprime (q p : ℕ) (β : MulAut S) : Prop :=
  ∀ s : S, β s = s → (∃ n : ℕ, s ^ q ^ n = 1) →
    s ∈ ⨆ (J : Subgroup S) (_ : IsChevSubOrCoprime q p β J), J

theorem qGenCoprime_of_qGen {q p : ℕ} {β : MulAut S} (h : Inputs256e.QGen q β) : QGenCoprime q p β := by
  intro s hs hq
  have hle : (⨆ (J : Subgroup S) (_ : Inputs256e.IsChevSub q β J), J) ≤
      ⨆ (J : Subgroup S) (_ : IsChevSubOrCoprime q p β J), J :=
    iSup₂_le fun J hJ => le_iSup₂_of_le (f := fun (J : Subgroup S) (_ : IsChevSubOrCoprime q p β J) => J) J
      (Or.inl hJ) le_rfl
  exact hle (h s hs hq)

end Defs

section Transport

variable {S T : Type} [Group S] [Group T]

theorem isChevSubOrCoprime_map {q p : ℕ} (e : S ≃* T) (β : MulAut S) {J : Subgroup S}
    (hJ : IsChevSubOrCoprime q p β J) :
    IsChevSubOrCoprime q p (MulAut.congr e β) (J.map (e : S →* T)) := by
  rcases hJ with hJ | ⟨hsn, hcop⟩
  · exact Or.inl (Inputs256e.isChevSub_map e β hJ)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [Inputs256e.fixSubgroup_congr]
      exact hsn.map (e : S →* T)
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hcop

theorem qGenCoprime_congr {q p : ℕ} (e : S ≃* T) (β : MulAut S) (h : QGenCoprime q p β) :
    QGenCoprime q p (MulAut.congr e β) := by
  intro t ht ⟨n, hn⟩
  have hs : β (e.symm t) = e.symm t := by
    have h1 : e (β (e.symm t)) = t := ht
    exact (e.eq_symm_apply).2 h1
  have hmem := h (e.symm t) hs ⟨n, by rw [← map_pow, hn, map_one]⟩
  have hle : (⨆ (J : Subgroup S) (_ : IsChevSubOrCoprime q p β J), J).map (e : S →* T) ≤
      ⨆ (J : Subgroup T) (_ : IsChevSubOrCoprime q p (MulAut.congr e β) J), J := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hJ => le_iSup₂_of_le (f := fun (J : Subgroup T)
      (_ : IsChevSubOrCoprime q p (MulAut.congr e β) J) => J) _ (isChevSubOrCoprime_map e β hJ) le_rfl
  have := hle (Subgroup.mem_map_of_mem (e : S →* T) hmem)
  simpa using this

theorem qGenCoprime_of_congr {q p : ℕ} (e : S ≃* T) (β : MulAut S) (h : QGenCoprime q p (MulAut.congr e β)) :
    QGenCoprime q p β := by
  have h1 := qGenCoprime_congr e.symm _ h
  have h2 : MulAut.congr e.symm (MulAut.congr e β) = β := by
    ext x
    simp [MulAut.congr]
  rwa [h2] at h1

theorem qGenCoprime_conj {q p : ℕ} (γ β : MulAut S) (h : QGenCoprime q p β) : QGenCoprime q p (γ * β * γ⁻¹) := by
  have hc : MulAut.congr (γ⁻¹ : S ≃* S) (γ * β * γ⁻¹) = β := by
    ext x
    show γ.symm (γ (β (γ.symm (γ x)))) = β x
    simp
  refine qGenCoprime_of_congr (γ⁻¹ : S ≃* S) (γ * β * γ⁻¹) ?_
  rw [hc]
  exact h

end Transport

section Central

variable {X T : Type} [Group X] [Finite X] [Group T]

theorem qGenCoprime_of_centralQuotient {q p : ℕ} (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (hcop : Nat.Coprime (Nat.card π.ker) q) (α : MulAut X)
    (β : MulAut T) (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (F : ι → Subgroup X)
    (hFα : ∀ i, F i ≤ fixSubgroup α)
    (hFn : ∀ i, ∀ c ∈ fixSubgroup α, ∀ g ∈ F i, c * g * c⁻¹ ∈ F i)
    (hF : ∀ i, (CFSG.Open.IsQuasisimple (F i) ∧ IsChevSimple q (F i ⧸ Subgroup.center (F i))) ∨
      Nat.Coprime (Nat.card (F i)) p)
    (hgen : ∀ x ∈ fixSubgroup α, (∃ n : ℕ, x ^ q ^ n = 1) → x ∈ ⨆ i, F i) : QGenCoprime q p β := by
  intro s hs ⟨n, hn⟩
  obtain ⟨x, hx, hxn⟩ := Inputs256e.exists_pow_lift π hπ hcop hn
  have hzk : x⁻¹ * α x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hx, hs, inv_mul_cancel]
  have hcomm : Commute x (α x) := by
    have hz : Commute x (x⁻¹ * α x) := Subgroup.mem_center_iff.1 (hker hzk) x
    have e : α x = x * (x⁻¹ * α x) := by group
    rw [e]
    exact (Commute.refl x).mul_right hz
  have hzq : (x⁻¹ * α x) ^ q ^ n = 1 := by
    rw [(hcomm.inv_left).mul_pow, inv_pow, hxn, ← map_pow, hxn, map_one, inv_one, one_mul]
  have hαx : α x = x := by
    have h1 := Inputs256e.eq_one_of_mem_of_coprime hcop hzk hzq
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hxF : x ∈ ⨆ i, F i := hgen x hαx ⟨n, hxn⟩
  have hNC : (fixSubgroup α).map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  have hNn : (((fixSubgroup α).map π).subgroupOf (fixSubgroup β)).Normal :=
    CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπ
  have hFS : ∀ i, IsChevSubOrCoprime q p β ((F i).map π) := by
    intro i
    have hsn : IsSubnormal ((F i).map π) (fixSubgroup β) :=
      IsSubnormal.step (Subgroup.map_mono (hFα i)) (Inputs256e.normal_map_subgroupOf_map π (hFn i))
        (IsSubnormal.step hNC hNn (IsSubnormal.refl _))
    rcases hF i with ⟨hFq, hFchev⟩ | hFcop
    · obtain ⟨hq, ⟨e⟩⟩ := Inputs256e.centralImage_facts π hker hFq
      exact Or.inl ⟨hsn, hq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e hFchev⟩
    · exact Or.inr ⟨hsn, Nat.Coprime.coprime_dvd_left (Subgroup.card_map_dvd (F i) π) hFcop⟩
  have hle : (⨆ i, F i).map π ≤ ⨆ (J : Subgroup T) (_ : IsChevSubOrCoprime q p β J), J := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun i => le_iSup₂_of_le (f := fun (J : Subgroup T) (_ : IsChevSubOrCoprime q p β J) => J) _
      (hFS i) le_rfl
  rw [← hx]
  exact hle (Subgroup.mem_map_of_mem π hxF)

end Central

section CoprimeLift

variable {K S : Type} [Group K] [Finite K] [Group S]

theorem exists_coprime_lift (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (a : MulAut K) (β : MulAut S) (hπβ : ∀ x, π (a x) = β (π x))
    {J : Subgroup S} (hJsn : IsSubnormal J (fixSubgroup β))
    (hcop : Nat.Coprime (Nat.card J) (Nat.card π.ker)) :
    ∃ J₀ : Subgroup K, IsSubnormal J₀ (fixSubgroup a) ∧ J₀.map π = J ∧ ∀ x ∈ J₀, x ^ Nat.card J = 1 := by
  classical
  set C : Subgroup K := fixSubgroup a with hCdef
  set N : Subgroup K := J.comap π with hNdef
  have hkerN : π.ker ≤ N := fun x hx => by
    rw [hNdef, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact J.one_mem
  set Z₀ : Subgroup ↥N := π.ker.subgroupOf N with hZ₀
  haveI : Z₀.Normal := Subgroup.Normal.subgroupOf (MonoidHom.normal_ker π) N
  have hZcard : Nat.card Z₀ = Nat.card π.ker := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerN).toEquiv
  have hZindex : Z₀.index = Nat.card J := by
    have h1 : (π.domRestrict N).ker = Z₀ := MonoidHom.ker_domRestrict N π
    have h2 : (π.domRestrict N).range = J := by
      rw [MonoidHom.domRestrict_range]
      exact Subgroup.map_comap_eq_self_of_surjective hπ J
    rw [← h1, Subgroup.index_ker, h2]
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime (N := Z₀)
    (by rw [hZcard, hZindex]; exact hcop.symm)
  have hHcard : Nat.card H = Nat.card J := by rw [← hH.symm.index_eq_card, hZindex]
  have hdec : ∀ n : ↥N, ∃ z ∈ Z₀, ∃ h ∈ H, n = z * h := fun n => by
    obtain ⟨⟨z, h⟩, hzh, -⟩ := hH.existsUnique n
    exact ⟨z.1, z.2, h.1, h.2, hzh.symm⟩
  set J₀ : Subgroup K := H.map N.subtype with hJ₀
  have hJ₀N : J₀ ≤ N := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hpow : ∀ x ∈ J₀, x ^ Nat.card J = 1 := by
    rintro _ ⟨h, hh, rfl⟩
    have h1 : (⟨h, hh⟩ : ↥H) ^ Nat.card H = 1 := pow_card_eq_one'
    rw [hHcard] at h1
    have h2 := congrArg (fun y : ↥H => ((y : ↥N) : K)) h1
    simpa using h2
  have hmap : J₀.map π = J := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hJ₀N hx
    · intro s hs
      obtain ⟨n₀, rfl⟩ := hπ s
      obtain ⟨z, hz, h, hh, hn⟩ := hdec ⟨n₀, hs⟩
      have hz' : π (z : K) = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_subgroupOf.1 hz)
      refine ⟨(h : K), ⟨h, hh, rfl⟩, ?_⟩
      have e : n₀ = (z : K) * (h : K) := congrArg Subtype.val hn
      rw [e, map_mul, hz', one_mul]
  have hJ₀C : J₀ ≤ C := by
    intro x hx
    rw [hCdef, mem_fixSubgroup]
    have hxJ : π x ∈ J := hJ₀N hx
    have hfix : π (a x) = π x := by rw [hπβ]; exact mem_fixSubgroup.1 (hJsn.le hxJ)
    have hzk : x⁻¹ * a x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, inv_mul_cancel]
    have hcomm : Commute x (x⁻¹ * a x) := Subgroup.mem_center_iff.1 (hker hzk) x
    have e : a x = x * (x⁻¹ * a x) := by group
    have hzm : (x⁻¹ * a x) ^ Nat.card J = 1 := by
      have h1 : (a x) ^ Nat.card J = 1 := by rw [← map_pow, hpow x hx, map_one]
      rw [e, hcomm.mul_pow, hpow x hx, one_mul] at h1
      exact h1
    have hzk' : (x⁻¹ * a x) ^ Nat.card π.ker = 1 := by
      have h1 := pow_card_eq_one' (G := π.ker) (x := ⟨x⁻¹ * a x, hzk⟩)
      exact congrArg Subtype.val h1
    have hord : orderOf (x⁻¹ * a x) ∣ Nat.gcd (Nat.card J) (Nat.card π.ker) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzm) (orderOf_dvd_of_pow_eq_one hzk')
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff, inv_mul_eq_one] at hord
    exact hord.symm
  have hCD : C.map π ≤ fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker a β hπβ
  have hJhsn : IsSubnormal (N ⊓ C) C := by
    have h2 : IsSubnormal (N ⊓ C) ((fixSubgroup β).comap π ⊓ C) := (hJsn.comap π).inf C
    rwa [inf_eq_right.2 (Subgroup.map_le_iff_le_comap.1 hCD)] at h2
  have hJ₀Jh : J₀ ≤ N ⊓ C := le_inf hJ₀N hJ₀C
  refine ⟨J₀, IsSubnormal.step hJ₀Jh ?_ hJhsn, hmap, hpow⟩
  rw [Subgroup.normal_subgroupOf_iff hJ₀Jh]
  intro x k hx hk
  obtain ⟨h₀, hh₀, rfl⟩ := hx
  obtain ⟨z, hz, h, hh, hk'⟩ := hdec ⟨k, hk.1⟩
  have hzc : (z : K) ∈ Subgroup.center K := hker (Subgroup.mem_subgroupOf.1 hz)
  have e : k = (z : K) * (h : K) := congrArg Subtype.val hk'
  have hcz : ∀ y : K, y * (z : K) = (z : K) * y := Subgroup.mem_center_iff.1 hzc
  have e2 : k * (h₀ : K) * k⁻¹ = (h : K) * (h₀ : K) * (h : K)⁻¹ := by
    calc k * (h₀ : K) * k⁻¹ = (z : K) * ((h : K) * (h₀ : K) * (h : K)⁻¹) * (z : K)⁻¹ := by
          rw [e]; group
      _ = (h : K) * (h₀ : K) * (h : K)⁻¹ := by rw [← hcz, mul_inv_cancel_right]
  change k * (h₀ : K) * k⁻¹ ∈ J₀
  rw [e2]
  exact ⟨h * h₀ * h⁻¹, H.mul_mem (H.mul_mem hh hh₀) (H.inv_mem hh), by simp⟩

end CoprimeLift

section Struct

open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)

variable {G : Type} [Group G] [Finite G]

theorem oPrimeResidualOf_le_of_qGenCoprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    {a : G} {K : Subgroup G} (hK : GLAPComponent p (Cg a) K) {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d) {z : ↥(Cg a)}
    (hzN : (z : G) ∈ Subgroup.normalizer (K : Set G))
    (hβ : QGenCoprime q p (Inputs2311c.catAct θ ⟨(z : G), hzN⟩)) :
    CFSG.GH74.GLS.oPrimeResidualOf q (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ≤
      GLAPPrimeCoreOf p (barX p (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) ⊔
        ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
          (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
            IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
          Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set zb : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) := QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z with hzb
  set C : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    barX p (Cg a) K ⊓ Subgroup.centralizer ({zb} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) with hC
  set R : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := GLAPPrimeCoreOf p C ⊔
    ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) (_ : GLAPComponent p C Q ∧
      IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))), Q with hR
  have hO : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hcopZ : Nat.Coprime (Nat.card (Subgroup.center (barOf p K))) q :=
    Inputs2311c.coprime_card_center hp hq hqp hO
  have hcopZp : ∀ m : ℕ, Nat.Coprime m p → Nat.Coprime m (Nat.card (Subgroup.center (barOf p K))) := by
    intro m hm
    refine Nat.coprime_of_dvd fun r hr hrm hrZ => ?_
    by_cases hrp : r = p
    · rw [hrp] at hrm
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_comm.1 hm) hrm
    · have h1 := Inputs2311c.coprime_card_center hp hr hrp hO
      exact (Nat.Prime.coprime_iff_not_dvd hr).1 (Nat.coprime_comm.1 h1) hrZ
  set zN : ↥N := ⟨(z : G), hzN⟩ with hzN'
  set α : MulAut (barOf p K) := barAut p K zN with hα
  set β : MulAut (Cat d) := Inputs2311c.catAct θ zN with hβdef
  set π : barOf p K →* Cat d := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf p K))) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center (barOf p K) := by
    ext x
    rw [MonoidHom.mem_ker]
    simp [π]
  have hπβ : ∀ y, π (α y) = β (π y) := fun y => (Inputs2311c.catAct_apply θ zN y).symm
  set f := quotEquivBarX hp hK.1 hK.2.1 with hf
  set F : barOf p K →* ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) :=
    (barX p (Cg a) K).subtype.comp f.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFα : ∀ y, F (α y) = zb * F y * zb⁻¹ := fun y => Lemma129b.quotEquivBarX_barAut hp hK z.2 hzN y
  have hFC : (fixSubgroup α).map F = C := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨(f y).2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have h := hFα y
      rw [show α y = y from hy] at h
      calc zb * F y = zb * F y * zb⁻¹ * zb := by group
        _ = F y * zb := by rw [← h]
    · intro hwCm
      obtain ⟨hwK, hwC⟩ := Subgroup.mem_inf.1 hwCm
      have hw : F (f.symm ⟨w, hwK⟩) = w := by simp [F]
      refine ⟨f.symm ⟨w, hwK⟩, ?_, hw⟩
      show α (f.symm ⟨w, hwK⟩) = f.symm ⟨w, hwK⟩
      apply hFinj
      rw [hFα, hw]
      have h1 : zb * w = w * zb := (Subgroup.mem_centralizer_iff.1 hwC) zb (Set.mem_singleton zb)
      rw [h1, mul_inv_cancel_right]
  set M : Subgroup (barOf p K) := ⨆ (L : Subgroup (barOf p K)) (_ : (IsSubnormal L (fixSubgroup α) ∧
      CFSG.Open.IsQuasisimple L ∧ IsChevSimple q (L ⧸ Subgroup.center L)) ∨
      (IsSubnormal L (fixSubgroup α) ∧ Nat.Coprime p (Nat.card L))), L with hM
  have hMπ : (⨆ (J : Subgroup (Cat d)) (_ : IsChevSubOrCoprime q p β J), J) ≤ M.map π := by
    refine iSup₂_le fun J hJ => ?_
    rcases hJ with ⟨hJsn, hJq, hJchev⟩ | ⟨hJsn, hJcop⟩
    · obtain ⟨L, hLsn, hLq, hLmap, ⟨e⟩⟩ :=
        Inputs256e.exists_quasisimple_lift π hπs hkerπ.le α β hπβ hJsn hJq
      rw [← hLmap]
      exact Subgroup.map_mono (le_iSup₂_of_le (f := fun (L : Subgroup (barOf p K))
        (_ : (IsSubnormal L (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple L ∧
          IsChevSimple q (L ⧸ Subgroup.center L)) ∨
          (IsSubnormal L (fixSubgroup α) ∧ Nat.Coprime p (Nat.card L))) => L) L
        (Or.inl ⟨hLsn, hLq, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e.symm hJchev⟩)
        le_rfl)
    · obtain ⟨L, hLsn, hLmap, hLpow⟩ := exists_coprime_lift π hπs hkerπ.le α β hπβ hJsn
        (by rw [hkerπ]; exact hcopZp _ hJcop)
      have hLcop : Nat.Coprime p (Nat.card L) :=
        Nat.coprime_comm.1 (Inputs256e.coprime_card_of_pow_eq_one hp hJcop hLpow)
      rw [← hLmap]
      exact Subgroup.map_mono (le_iSup₂_of_le (f := fun (L : Subgroup (barOf p K))
        (_ : (IsSubnormal L (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple L ∧
          IsChevSimple q (L ⧸ Subgroup.center L)) ∨
          (IsSubnormal L (fixSubgroup α) ∧ Nat.Coprime p (Nat.card L))) => L) L
        (Or.inr ⟨hLsn, hLcop⟩) le_rfl)
  have hLR : ∀ L : Subgroup (barOf p K), (IsSubnormal L (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple L ∧
      IsChevSimple q (L ⧸ Subgroup.center L)) ∨ (IsSubnormal L (fixSubgroup α) ∧ Nat.Coprime p (Nat.card L)) →
      L.map F ≤ R := by
    rintro L (⟨hLsn, hLq, hLchev⟩ | ⟨hLsn, hLcop⟩)
    · have hsn : IsSubnormal (L.map F) C := by rw [← hFC]; exact hLsn.map F
      set eL : L ≃* L.map F := Subgroup.equivMapOfInjective L F hFinj with heL
      have hq' : CFSG.Open.IsQuasisimple (L.map F) := hLq.of_mulEquiv eL.symm
      have e₂ : (L ⧸ Subgroup.center L) ≃* (L.map F ⧸ Subgroup.center (L.map F)) :=
        QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
      by_cases hpL : p ∣ Nat.card (L.map F ⧸ Subgroup.center (L.map F))
      · refine le_sup_of_le_right (le_iSup₂_of_le (f := fun (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
          (_ : GLAPComponent p C Q ∧ IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))) => Q)
          (L.map F) ⟨?_, ?_⟩ le_rfl)
        · exact CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hsn hq' hpL
        · obtain ⟨e'⟩ := Inputs256e.nonempty_pSimple_equiv hp hq' hpL
          exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e₂.trans e') hLchev
      · exact le_sup_of_le_left
          (Inputs256e.le_glaPPrimeCoreOf_of_isSubnormal' hp hsn
            (Inputs256e.coprime_card_of_perfect hq'.1 hp hpL))
    · have hsn : IsSubnormal (L.map F) C := by rw [← hFC]; exact hLsn.map F
      refine le_sup_of_le_left (Inputs256e.le_glaPPrimeCoreOf_of_isSubnormal' hp hsn ?_)
      rw [Subgroup.card_map_of_injective hFinj]
      exact hLcop
  have hMR : M.map F ≤ R := by
    rw [hM, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hL => hLR L hL
  rw [CFSG.GH74.GLS.oPrimeResidualOf, Subgroup.map_le_iff_le_comap, CFSG.GH74.GLS.oPrimeResidual,
    Subgroup.closure_le]
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  have hxn : (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ^ q ^ n = 1 := by
    have h := congrArg Subtype.val hn
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  have hxC : (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ∈ (fixSubgroup α).map F := by rw [hFC]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hxC
  show (x : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) ∈ R
  rw [← hyx]
  have hyn : y ^ q ^ n = 1 := hFinj (by rw [map_pow, map_one, hyx]; exact hxn)
  have hs : π y ∈ ⨆ (J : Subgroup (Cat d)) (_ : IsChevSubOrCoprime q p β J), J :=
    hβ (π y) (by rw [← hπβ, show α y = y from hy]) ⟨n, by rw [← map_pow, hyn, map_one]⟩
  obtain ⟨m, hm, hmy⟩ := hMπ hs
  have hz : m⁻¹ * y ∈ Subgroup.center (barOf p K) := by
    rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hmy, inv_mul_cancel]
  have hyM : y ∈ M := Inputs256e.mem_of_mul_central le_rfl hcopZ hm hz hyn
  exact hMR (Subgroup.mem_map_of_mem F hyM)

theorem barX_le_iSup_glaPComponent_of_gen {p q : ℕ} (hp : p.Prime) {a : G} {K A0 : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) {d : TauCeti.ValidLieTypeIndex}
    (θ : barOf p K ⧸ Subgroup.center (barOf p K) ≃* Cat d) (hN : A0 ≤ Subgroup.normalizer (K : Set G))
    (hgen : (⊤ : Subgroup (Cat d)) ≤ ⨆ (z : ↥(Cg a)) (hz : (z : G) ∈ A0) (_ : z ≠ 1),
      ⨆ (J : Subgroup (Cat d)) (_ : Inputs256e.IsChevSub q (Inputs2311c.catAct θ ⟨(z : G), hN hz⟩) J ∧
        p ∣ Nat.card (J ⧸ Subgroup.center J)), J) :
    barX p (Cg a) K ≤
      ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ A0) (_ : z ≠ 1),
        ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
          (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
            IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))),
          Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set R₂ : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ A0) (_ : z ≠ 1),
      ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
        (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
          IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))), Q with hR₂
  set π : barOf p K →* Cat d := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf p K))) with hπ
  have hπs : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center (barOf p K) := by
    ext x
    rw [MonoidHom.mem_ker]
    simp [π]
  set f := quotEquivBarX hp hK.1 hK.2.1 with hf
  set F : barOf p K →* ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) :=
    (barX p (Cg a) K).subtype.comp f.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp f.injective
  have hFC : ∀ (z : ↥(Cg a)) (hzN : (z : G) ∈ Subgroup.normalizer (K : Set G)),
      (fixSubgroup (barAut p K ⟨(z : G), hzN⟩)).map F = barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))) := by
    intro z hzN
    set zb : ↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a) := QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z with hzb
    have hFα : ∀ y, F (barAut p K ⟨(z : G), hzN⟩ y) = zb * F y * zb⁻¹ := fun y =>
      Lemma129b.quotEquivBarX_barAut hp hK z.2 hzN y
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨(f y).2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have h := hFα y
      rw [show barAut p K ⟨(z : G), hzN⟩ y = y from hy] at h
      calc zb * F y = zb * F y * zb⁻¹ * zb := by group
        _ = F y * zb := by rw [← h]
    · intro hwCm
      obtain ⟨hwK, hwC⟩ := Subgroup.mem_inf.1 hwCm
      have hw : F (f.symm ⟨w, hwK⟩) = w := by simp [F]
      refine ⟨f.symm ⟨w, hwK⟩, ?_, hw⟩
      show barAut p K ⟨(z : G), hzN⟩ (f.symm ⟨w, hwK⟩) = f.symm ⟨w, hwK⟩
      apply hFinj
      rw [hFα, hw]
      have h1 : zb * w = w * zb := (Subgroup.mem_centralizer_iff.1 hwC) zb (Set.mem_singleton zb)
      rw [h1, mul_inv_cancel_right]
  set M : Subgroup (barOf p K) := R₂.comap F with hM
  have hJM : ∀ (z : ↥(Cg a)) (hz : (z : G) ∈ A0), z ≠ 1 → ∀ J : Subgroup (Cat d),
      Inputs256e.IsChevSub q (Inputs2311c.catAct θ ⟨(z : G), hN hz⟩) J →
      p ∣ Nat.card (J ⧸ Subgroup.center J) → J ≤ M.map π := by
    intro z hz hz1 J ⟨hJsn, hJq, hJchev⟩ hpJ
    have hπβ : ∀ y, π (barAut p K ⟨(z : G), hN hz⟩ y) =
        Inputs2311c.catAct θ ⟨(z : G), hN hz⟩ (π y) := fun y =>
      (Inputs2311c.catAct_apply θ ⟨(z : G), hN hz⟩ y).symm
    obtain ⟨L, hLsn, hLq, hLmap, ⟨e⟩⟩ :=
      Inputs256e.exists_quasisimple_lift π hπs hkerπ.le _ _ hπβ hJsn hJq
    rw [← hLmap]
    refine Subgroup.map_mono fun y hy => ?_
    show F y ∈ R₂
    have hsn : IsSubnormal (L.map F) (barX p (Cg a) K ⊓ Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) := by
      rw [← hFC z (hN hz)]
      exact hLsn.map F
    set eL : L ≃* L.map F := Subgroup.equivMapOfInjective L F hFinj with heL
    have hq' : CFSG.Open.IsQuasisimple (L.map F) := hLq.of_mulEquiv eL.symm
    have e₂ : (L ⧸ Subgroup.center L) ≃* (L.map F ⧸ Subgroup.center (L.map F)) :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    have hpL : p ∣ Nat.card (L.map F ⧸ Subgroup.center (L.map F)) := by
      rw [← Nat.card_congr e₂.toEquiv, Nat.card_congr e.toEquiv]
      exact hpJ
    have hcomp := CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple hp hsn hq' hpL
    obtain ⟨e'⟩ := Inputs256e.nonempty_pSimple_equiv hp hq' hpL
    have hchev : IsChevSimple q (barOf p (L.map F) ⧸ Subgroup.center (barOf p (L.map F))) :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr (e₂.trans e')
        (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr e.symm hJchev)
    have hLR : L.map F ≤ R₂ := by
      rw [hR₂]
      refine le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hz1 ?_))
      exact le_iSup₂_of_le (f := fun (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))
        (_ : GLAPComponent p (barX p (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q ∧
          IsChevSimple q (barOf p Q ⧸ Subgroup.center (barOf p Q))) => Q) (L.map F) ⟨hcomp, hchev⟩ le_rfl
    exact hLR (Subgroup.mem_map_of_mem F hy)
  have hMπ : (⊤ : Subgroup (Cat d)) ≤ M.map π := by
    refine hgen.trans (iSup_le fun z => iSup_le fun hz => iSup_le fun hz1 => iSup₂_le fun J hJ => ?_)
    exact hJM z hz hz1 J hJ.1 hJ.2
  have hdec : ∀ y : barOf p K, ∃ m ∈ M, m⁻¹ * y ∈ Subgroup.center (barOf p K) := by
    intro y
    obtain ⟨m, hm, hmy⟩ := hMπ (Subgroup.mem_top (π y))
    refine ⟨m, hm, ?_⟩
    rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hmy, inv_mul_cancel]
  have hperf : commutator (barOf p K) = ⊤ := (l119_isQuasisimple_barOf hp hK).1
  have hMtop : M = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hperf, _root_.commutator_def, Subgroup.commutator_le]
    intro y₁ _ y₂ _
    obtain ⟨m₁, hm₁, hz₁⟩ := hdec y₁
    obtain ⟨m₂, hm₂, hz₂⟩ := hdec y₂
    have e₁ : y₁ = m₁ * (m₁⁻¹ * y₁) := (mul_inv_cancel_left m₁ y₁).symm
    have e₂ : y₂ = m₂ * (m₂⁻¹ * y₂) := (mul_inv_cancel_left m₂ y₂).symm
    rw [e₁, e₂, commutatorElement_def, commutator_mul_central hz₁ hz₂, ← commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  intro w hw
  have hwF : F (f.symm ⟨w, hw⟩) = w := by simp [F]
  rw [← hwF]
  have hmem : f.symm ⟨w, hw⟩ ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  exact hmem

theorem false_of_ambiguousChev_three
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {a : G}
    {K A0 : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    (hamb : CFSG.Yardstones.Md0ec50421ce4.catalogIs (barOf p K ⧸ Subgroup.center (barOf p K))
      (CFSG.Yardstones.Md0ec50421ce4.ambiguousChev 3))
    (hA0el : IsElemAbelian p A0) (hA0r : 2 ≤ CFSG.Open.pRank p A0)
    (hN : A0 ≤ Subgroup.normalizer (K : Set G)) (hF : ∀ x ∈ A0, x ∈ centBar p ⊤ K → x = 1) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, h | h⟩ | ⟨rfl, h | -⟩ | ⟨-, h⟩
    · omega
    · omega
    · omega
    · have h := (Inputs256e.sq_dvd_card_mulAut hp hK e hA0el hA0r hN hF).trans InputsSeitz.card_mulAut_alt6_dvd
      exact Inputs256e.not_sq_dvd_1440 hp hp2 hp3 h
    · omega
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | A k Q =>
      rcases k with _ | _ | k
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · have h8 : Q.card = 8 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
        have : Fact Q.p.Prime := ⟨Q.prime_p⟩
        set F := GaloisField Q.p Q.exponent
        have hF8 : Nat.card F = 2 ^ 3 := by
          rw [GaloisField.card _ _ Q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, h8]
          norm_num
        let e' : barOf p K ⧸ Subgroup.center (barOf p K) ≃* CFSG.GorensteinWalter.PSL2 F :=
          e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 Q hv)
        have h := Inputs256e.sq_dvd_card_mulAut hp hK e' hA0el hA0r hN hF
        have hAutF : Nat.card (F ≃+* F) = 3 := by
          obtain ⟨-, -, -, -, h3, -⟩ :=
            CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
              Nat.prime_two (n := 3) (by norm_num) hF8
          exact h3
        rw [CFSG.GH74.GLS.IVK.Proofs2.ivk93m12_card_aut_psl2, hAutF, hF8] at h
        norm_num at h
        exact Inputs256e.not_sq_dvd_1512 hp hp2 hp3 h
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | twistedA k Q =>
      rcases k with _ | _ | _ | _ | k
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      · have hQ2 : Q.card = 2 := by simpa [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] using hi
        have : Fact Q.p.Prime := ⟨Q.prime_p⟩
        have hQ2' : Q.p ^ Q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hQ2
        obtain ⟨hQp, hQe⟩ := (Nat.prime_two.pow_eq_iff).1 hQ2'
        obtain ⟨⟨hℓ, hf, hn3, hq⟩, Kf, _, _, hKf, ⟨eT⟩⟩ :=
          CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv (MulEquiv.refl _)
        have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData Q.p Q.exponent Kf :=
          ⟨hℓ, hf, by rw [hKf, ← pow_mul, mul_comm]⟩
        obtain ⟨eP⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv h
          (CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram (n := 3 + 1) (K := Kf))
        let e' : Cat ⟨.twistedA 3 Q, hv⟩ ≃*
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
              (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Kf (3 + 1)) :=
          (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm).trans eP.symm
        have hq' : ¬(3 + 1 = 3 ∧ Q.p ^ Q.exponent = 2) := fun h3 => by omega
        have hC : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram (1 : GL (Fin (3 + 1)) Kf) :=
          CFSG.RankThree.PartOne.KCUnitaryModel.isPrimeFormGram_idGram
        obtain ⟨-, -, -, -, -, -, hsurj, hkerD, -, hinn, hDI⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_prime_form_full_semilinear_realization h hC
            hn3 hq'
        have h1 := Inputs256e.sq_dvd_card_mulAut hp hK (e.trans e') hA0el hA0r hN hF
        have hAut : Nat.card (MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Kf (3 + 1)))) =
            Nat.card (Kf ≃+* Kf) * Nat.card (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
              ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf)) := by
          have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC hn3 hq').ker
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv] at e1
          rw [e1, hkerD]
        have hKf4 : Nat.card Kf = 2 ^ 2 := by rw [hKf, hQp, hQe]; norm_num
        obtain ⟨-, -, -, -, hAutK, -⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality Nat.prime_two
            (n := 2) (by norm_num) hKf4
        set P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
          ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf) with hPdef
        set D := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormD h
          ((1 : GL (Fin (3 + 1)) Kf) : Matrix (Fin (3 + 1)) (Fin (3 + 1)) Kf) with hDdef
        have hinnD : CFSG.ComponentClassification.OuterAutomorphisms.inner P ≤ D := by
          intro α hα
          obtain ⟨s, rfl⟩ := (hinn α).1 hα
          exact ⟨_, rfl⟩
        have hD : Nat.card D =
            Nat.card (D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D) *
              Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner P) := by
          rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
              ((CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D),
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinnD).toEquiv]
        have hP : Nat.card P = 25920 := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 3 Q, hv⟩ P ⟨e'.symm⟩]
          show CFSG.Open.orderTwistedA 3 Q.card = 25920
          rw [hQ2]
          decide
        have hinnP : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner P) ∣ 25920 := by
          rw [← hP]
          exact Subgroup.card_range_dvd (MulAut.conj : P →* MulAut P)
        have hDI3 : Nat.card (D ⧸ (CFSG.ComponentClassification.OuterAutomorphisms.inner P).subgroupOf D) ∣ 3 := by
          have := hDI
          rwa [hQ2'] at this
        have hdvd : Nat.card (MulAut P) ∣ 155520 := by
          rw [hAut, hAutK, hD]
          exact (mul_dvd_mul_left 2 (mul_dvd_mul hDI3 hinnP)).trans (by norm_num)
        exact Inputs256e.not_sq_dvd_155520 hp hp2 hp3 (h1.trans hdvd)
      · simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi

end Struct

section Reduction

open CFSG.LieType.SeitzGeneration (Cat IsLinearIndex IsUnitaryIndex')
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)

@[expose] def QGen3On (P : TauCeti.ValidLieTypeIndex → ℕ → Prop) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → P d p →
    ∀ β : MulAut (Cat d), orderOf β = p → QGenCoprime 3 p β

@[expose] def QGen3SympOrth : Prop :=
  QGen3On fun d _ => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .symplecticOrthogonal

@[expose] def QGen3Exc : Prop :=
  QGen3On fun d _ => CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional

@[expose] def QGen3Ree : Prop :=
  QGen3On fun d p => (∃ m, d.1 = .reeG2 m) ∧ ¬ (d.1 = .reeG2 3 ∧ p = 7)

@[expose] def Input14_2StructRee37 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {a : G} {K E A : Subgroup G}, GLAPComponent 7 (Cg a) K →
    (∃ hv : (TauCeti.LieTypeIndex.reeG2 3).Valid,
      Nonempty (barOf 7 K ⧸ Subgroup.center (barOf 7 K) ≃* Cat ⟨.reeG2 3, hv⟩)) →
    E ⊓ A ≤ Cg a → IsElemAbelian 7 (E ⊓ A) → 2 ≤ CFSG.Open.pRank 7 (E ⊓ A) →
    E ⊓ A ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ E ⊓ A, x ∈ centBar 7 ⊤ K → x = 1) →
    ¬ Prop1116Iii 7 3 E A K →
    (∀ z : ↥(Cg a), (z : G) ∈ E ⊓ A → z ≠ 1 →
      CFSG.GH74.GLS.oPrimeResidualOf 3 (barX 7 (Cg a) K ⊓ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore 7 ↥(Cg a)) z} : Set (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))) ≤
        GLAPPrimeCoreOf 7 (barX 7 (Cg a) K ⊓ Subgroup.centralizer
            ({QuotientGroup.mk' (GLAPPrimeCore 7 ↥(Cg a)) z} :
              Set (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))) ⊔
          ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))
            (_ : GLAPComponent 7 (barX 7 (Cg a) K ⊓ Subgroup.centralizer
                ({QuotientGroup.mk' (GLAPPrimeCore 7 ↥(Cg a)) z} :
                  Set (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))) Q ∧
              IsChevSimple 3 (barOf 7 Q ⧸ Subgroup.center (barOf 7 Q))),
            Q) ∨
    barX 7 (Cg a) K ≤
      ⨆ (z : ↥(Cg a)) (_ : (z : G) ∈ E ⊓ A) (_ : z ≠ 1),
        ⨆ (Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))
          (_ : GLAPComponent 7 (barX 7 (Cg a) K ⊓ Subgroup.centralizer
              ({QuotientGroup.mk' (GLAPPrimeCore 7 ↥(Cg a)) z} :
                Set (↥(Cg a) ⧸ GLAPPrimeCore 7 ↥(Cg a)))) Q ∧
            IsChevSimple 3 (barOf 7 Q ⧸ Subgroup.center (barOf 7 Q))),
          Q

@[expose] def ReeGen37 : Prop :=
  ∀ (hv : (TauCeti.LieTypeIndex.reeG2 3).Valid) (B : Subgroup (MulAut (Cat ⟨.reeG2 3, hv⟩))),
    IsElemAbelian 7 B → 49 ≤ Nat.card B →
      (⊤ : Subgroup (Cat ⟨.reeG2 3, hv⟩)) ≤ ⨆ (β : MulAut (Cat ⟨.reeG2 3, hv⟩)) (_ : β ∈ B) (_ : β ≠ 1),
        ⨆ (J : Subgroup (Cat ⟨.reeG2 3, hv⟩))
          (_ : Inputs256e.IsChevSub 3 β J ∧ 7 ∣ Nat.card (J ⧸ Subgroup.center J)), J

theorem input14_2StructRee37_of_gen (h : ReeGen37) : Input14_2StructRee37 := by
  intro G _ _ a K E A hK ⟨hv, ⟨θ⟩⟩ hA0C hA0el hA0r hN hF hIii
  right
  haveI : Fact (7 : ℕ).Prime := ⟨by norm_num⟩
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  set B : Subgroup (MulAut (Cat ⟨.reeG2 3, hv⟩)) := ((E ⊓ A).subgroupOf N).map (Inputs2311c.catAct θ) with hB
  have hBel : IsElemAbelian 7 B := (hA0el.subgroupOf N).map _
  have hinj : ∀ x ∈ (E ⊓ A).subgroupOf N, Inputs2311c.catAct θ x = 1 → x = 1 := fun x hx h1 =>
    Subtype.ext (Inputs256e.catAct_eq_one (by norm_num) hK θ hF (Subgroup.mem_subgroupOf.1 hx) h1)
  have hBcard : 49 ≤ Nat.card B := by
    set g := (Inputs2311c.catAct θ).domRestrict ((E ⊓ A).subgroupOf N) with hg
    have hginj : Function.Injective g := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).2 (Subtype.ext (hinj x.1 x.2 (MonoidHom.mem_ker.1 hx)))
    have h1 : Nat.card B = Nat.card ((E ⊓ A).subgroupOf N) := by
      rw [hB, ← MonoidHom.domRestrict_range]
      exact (Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv).symm
    have h2 : Nat.card ((E ⊓ A).subgroupOf N) = Nat.card ↥(E ⊓ A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
    obtain ⟨D, hDA, -, hDc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA0r
    have h3 : 7 ^ 2 ∣ Nat.card ↥(E ⊓ A) := hDc ▸ Subgroup.card_dvd_of_le hDA
    rw [h1, h2]
    exact Nat.le_of_dvd Nat.card_pos (by simpa using h3)
  refine barX_le_iSup_glaPComponent_of_gen (by norm_num) hK θ hN ((h hv B hBel hBcard).trans ?_)
  refine iSup_le fun β => iSup_le fun hβ => iSup_le fun hβ1 => ?_
  obtain ⟨x, hx, rfl⟩ := hβ
  have hxA : ((x : N) : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hx
  have hx1 : (⟨((x : N) : G), hA0C hxA⟩ : ↥(Cg a)) ≠ 1 := fun h1 => hβ1 (by
    have hx1' : (x : G) = 1 := congrArg Subtype.val h1
    have : x = 1 := Subtype.ext hx1'
    rw [this, map_one])
  refine le_iSup_of_le ⟨((x : N) : G), hA0C hxA⟩ (le_iSup_of_le hxA (le_iSup_of_le hx1 ?_))
  exact le_rfl

theorem qGen3On_of_families (hL : QGen3On fun d _ => IsLinearIndex d.1)
    (hU : QGen3On fun d _ => IsUnitaryIndex' d.1) (hSO : QGen3SympOrth) (hE : QGen3Exc) (hR : QGen3Ree) :
    QGen3On fun d p => ¬ (d.1 = .reeG2 3 ∧ p = 7) := by
  rintro ⟨d, hv⟩ hd3 p hp hp2 hp3 hP β hβ
  cases d with
  | A m q => exact hL ⟨_, hv⟩ hd3 p hp hp2 hp3 ⟨m, q, rfl⟩ β hβ
  | twistedA m q => exact hU ⟨_, hv⟩ hd3 p hp hp2 hp3 ⟨m, q, rfl⟩ β hβ
  | B m q => exact hSO ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | C m q => exact hSO ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | D m q => exact hSO ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | twistedD m q => exact hSO ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | E6 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | E7 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | E8 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | F4 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | G2 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | twistedE6 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | trialityD4 q => exact hE ⟨_, hv⟩ hd3 p hp hp2 hp3 rfl β hβ
  | reeG2 m => exact hR ⟨_, hv⟩ hd3 p hp hp2 hp3 ⟨⟨m, rfl⟩, hP⟩ β hβ
  | suzuki m => exact absurd hd3 (by simp)
  | reeF4 m => exact absurd hd3 (by simp)
  | tits => exact absurd hd3 (by simp)

variable {G : Type} [Group G] [Finite G]

theorem input14_2StructThree_of_qGen3On
    (hQ : QGen3On fun d p => ¬ (d.1 = .reeG2 3 ∧ p = 7)) (hRee : Input14_2StructRee37) :
    Inputs256e.Input14_2StructThree := by
  intro G _ _ p q hp hp2 hq hq2 hqp hq3 a K E A hK hchev hA0C hA0el hA0r hN hF hIii
  subst hq3
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := Ne.symm hqp
  rcases hchev with ⟨i, hi, ⟨θ⟩⟩ | hamb
  · cases i with
    | lie d =>
      have hdq : d.1.characteristic = 3 := hi
      by_cases hR : d.1 = .reeG2 3 ∧ p = 7
      · obtain ⟨hd, rfl⟩ := hR
        obtain ⟨d1, hv⟩ := d
        simp only at hd
        subst hd
        exact hRee hK ⟨hv, ⟨θ⟩⟩ hA0C hA0el hA0r hN hF hIii
      · left
        intro z hzA hz1
        have hzN : (z : G) ∈ Subgroup.normalizer (K : Set G) := hN hzA
        have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
        have hord : orderOf (Inputs2311c.catAct θ ⟨(z : G), hzN⟩) = p := by
          have hzp : (⟨(z : G), hzN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
            Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hA0el.2 _ hzA)
          refine orderOf_eq_prime (by rw [← map_pow, hzp, map_one]) fun h1 => hz1' ?_
          exact Inputs256e.catAct_eq_one hp hK θ hF hzA h1
        exact oPrimeResidualOf_le_of_qGenCoprime hp hq hqp hK θ hzN (hQ d hdq p hp hp2 hp3 hR _ hord)
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · exact (false_of_ambiguousChev_three hp hp2 hp3 hK hamb hA0el hA0r hN hF).elim

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256i

end
