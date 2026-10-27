module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourA6Core
public import CFSG.Alternating.Multipliers.OddKernel
public import CFSG.CGT.PushingUpLit.CGT6.SixFourA6Gen

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

section Helpers

variable {Q V : Type*} [Group Q] [Group V]

@[expose] def kerAct (θ : Q →* MulAut V) (W : Subgroup V) : Subgroup Q where
  carrier := {k | ∀ w ∈ W, θ k w = w}
  one_mem' := fun w _ => by simp
  mul_mem' := by
    intro k₁ k₂ h₁ h₂ w hw
    rw [map_mul, MulAut.mul_apply, h₂ w hw, h₁ w hw]
  inv_mem' := by
    intro k hk w hw
    have := hk w hw
    have h2 : θ k⁻¹ (θ k w) = θ k⁻¹ w := by rw [this]
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
    exact h2.symm

theorem mem_kerAct {θ : Q →* MulAut V} {W : Subgroup V} {k : Q} :
    k ∈ kerAct θ W ↔ ∀ w ∈ W, θ k w = w := Iff.rfl

theorem kerAct_normal (θ : Q →* MulAut V) {W : Subgroup V} (hW : ∀ k : Q, ∀ w ∈ W, θ k w ∈ W) :
    (kerAct θ W).Normal :=
  ⟨fun k hk g w hw => by
    have h1 : θ g⁻¹ w ∈ W := hW g⁻¹ w hw
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hk _ h1]
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩

theorem card_le_index_of_inf_eq_bot {A C : Subgroup V} [Finite V] (h : A ⊓ C = ⊥) :
    Nat.card A ≤ C.index := by
  have hinj : Function.Injective (fun a : A => (QuotientGroup.mk (a : V) : V ⧸ C)) := by
    intro a a' haa
    have h1 : (a : V)⁻¹ * a' ∈ C := QuotientGroup.eq.mp haa
    have h2 : (a : V)⁻¹ * a' ∈ A := A.mul_mem (A.inv_mem a.2) a'.2
    have h3 : (a : V)⁻¹ * a' ∈ A ⊓ C := ⟨h2, h1⟩
    rw [h] at h3
    exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp h3))
  have := Nat.card_le_card_of_injective _ hinj
  exact this

theorem trivial_mod_ker [Finite V] (hc : ∀ a b : V, a * b = b * a)
    {ζ β : MulAut V} (hζ : ζ ^ 3 = 1) (hβζ : β * ζ = ζ * β) (hββ : β * β = 1)
    {Φ : V →* V} (hΦζ : ∀ v, Φ (ζ v) = ζ (Φ v)) (hℓ4 : Nat.card Φ.range = 4)
    (hfix : Φ.range ⊓ autFixSub ζ = ⊥) (hβH : ∀ h ∈ Φ.ker, β h ∈ Φ.ker) :
    ∀ v, Φ (β v) = Φ v := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hfin : Finite Φ.range := Nat.finite_of_card_ne_zero (by rw [hℓ4]; norm_num)
  have hζ3 : ∀ v, ζ (ζ (ζ v)) = v := fun v => by
    have : (ζ ^ 3) v = v := by rw [hζ]; rfl
    simpa [pow_succ, MulAut.mul_apply] using this
  have hβζ' : ∀ v, β (ζ v) = ζ (β v) := fun v => by
    rw [← MulAut.mul_apply, hβζ, MulAut.mul_apply]
  have hββ' : ∀ v, β (β v) = v := fun v => by
    rw [← MulAut.mul_apply, hββ]; rfl
  have hkerζ : ∀ h ∈ Φ.ker, ζ h ∈ Φ.ker := fun h hh => by
    rw [MonoidHom.mem_ker] at hh ⊢
    rw [hΦζ, hh, map_one]
  have hfpf : ∀ u ∈ Φ.range, ζ u = u → u = 1 := by
    intro u hu hzu
    have : u ∈ Φ.range ⊓ autFixSub ζ := ⟨hu, hzu⟩
    rw [hfix] at this
    exact Subgroup.mem_bot.mp this
  have hne : Φ.range ≠ ⊥ := by
    intro h
    rw [h] at hℓ4
    simp at hℓ4
  obtain ⟨⟨u₀, ⟨v₀, hv₀⟩⟩, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hΦv₀ : Φ v₀ = u₀ := hv₀
  set v₁ : V := ζ v₀ with hv₁
  set v₂ : V := ζ v₁ with hv₂
  set u₁ : V := ζ u₀ with hu₁
  set u₂ : V := ζ u₁ with hu₂
  have hΦv₁ : Φ v₁ = u₁ := by rw [hv₁, hΦζ, hΦv₀]
  have hΦv₂ : Φ v₂ = u₂ := by rw [hv₂, hΦζ, hΦv₁]
  have hu₀r : u₀ ∈ Φ.range := ⟨v₀, hΦv₀⟩
  have hu₁r : u₁ ∈ Φ.range := ⟨v₁, hΦv₁⟩
  have hu₂r : u₂ ∈ Φ.range := ⟨v₂, hΦv₂⟩
  have hu₁u₀ : u₁ ≠ u₀ := fun h => hu₀1' (hfpf u₀ hu₀r h)
  have hu₁1 : u₁ ≠ 1 := fun h => hu₀1' (ζ.injective (by rw [← hu₁, h, map_one]))
  have hu₂1 : u₂ ≠ 1 := fun h => hu₁1 (ζ.injective (by rw [← hu₂, h, map_one]))
  have hu₂u₁ : u₂ ≠ u₁ := fun h => hu₁1 (hfpf u₁ hu₁r h)
  have hu₂u₀ : u₂ ≠ u₀ := by
    intro h
    apply hu₁u₀
    have := congrArg ζ h
    rw [hu₂, hu₁] at this
    rw [hζ3] at this
    rw [hu₁]; exact this.symm
  have hall : ∀ u ∈ Φ.range, u = 1 ∨ u = u₀ ∨ u = u₁ ∨ u = u₂ :=
    mem_of_card_eq_four hℓ4 Φ.range.one_mem hu₀r hu₁r hu₂r hu₀1'.symm hu₁1.symm hu₂1.symm
      hu₁u₀.symm hu₂u₀.symm hu₂u₁.symm
  have hΦh : ∀ x y : V, Φ x = Φ y → x * y⁻¹ ∈ Φ.ker := fun x y h => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h]; exact mul_inv_cancel _
  have hkey : Φ (β v₀) = u₀ := by
    have hmem : Φ (β v₀) ∈ Φ.range := ⟨β v₀, rfl⟩
    rcases hall _ hmem with h | h | h | h
    · exfalso
      have hk : β v₀ ∈ Φ.ker := h
      have := hβH _ hk
      rw [hββ'] at this
      exact hu₀1' (hΦv₀ ▸ this)
    · exact h
    · exfalso
      obtain ⟨h₁, hh₁⟩ : ∃ h₁ : V, h₁ = β v₀ * v₁⁻¹ := ⟨_, rfl⟩
      have hh : h₁ ∈ Φ.ker := by rw [hh₁]; exact hΦh (β v₀) v₁ (by rw [h, hΦv₁])
      have e1 : β v₀ = h₁ * v₁ := by rw [hh₁, inv_mul_cancel_right]
      have e2 : v₀ = v₂ * ζ h₁ * β h₁ := by
        calc v₀ = β (β v₀) := (hββ' v₀).symm
          _ = β (h₁ * v₁) := by rw [← e1]
          _ = β h₁ * β v₁ := by rw [map_mul]
          _ = β h₁ * ζ (β v₀) := by rw [hv₁, hβζ']
          _ = β h₁ * ζ (h₁ * v₁) := by rw [← e1]
          _ = v₂ * ζ h₁ * β h₁ := by rw [map_mul, hv₂]; ac_rfl
      have := congrArg Φ e2
      rw [map_mul, map_mul, hΦv₂, (MonoidHom.mem_ker.mp (hkerζ _ hh)), (MonoidHom.mem_ker.mp (hβH _ hh)),
        mul_one, mul_one, hΦv₀] at this
      exact hu₂u₀ this.symm
    · exfalso
      obtain ⟨h₁, hh₁⟩ : ∃ h₁ : V, h₁ = β v₀ * v₂⁻¹ := ⟨_, rfl⟩
      have hh : h₁ ∈ Φ.ker := by rw [hh₁]; exact hΦh (β v₀) v₂ (by rw [h, hΦv₂])
      have e1 : β v₀ = h₁ * v₂ := by rw [hh₁, inv_mul_cancel_right]
      have hzz : ζ (ζ v₂) = v₁ := by
        have : ζ (ζ v₂) = ζ (ζ (ζ (ζ v₀))) := by rw [hv₂, hv₁]
        rw [this, hζ3 (ζ v₀)]
      have e2 : v₀ = v₁ * ζ (ζ h₁) * β h₁ := by
        calc v₀ = β (β v₀) := (hββ' v₀).symm
          _ = β (h₁ * v₂) := by rw [← e1]
          _ = β h₁ * β v₂ := by rw [map_mul]
          _ = β h₁ * ζ (ζ (β v₀)) := by rw [hv₂, hv₁, hβζ', hβζ']
          _ = β h₁ * ζ (ζ (h₁ * v₂)) := by rw [← e1]
          _ = v₁ * ζ (ζ h₁) * β h₁ := by rw [map_mul, map_mul, hzz]; ac_rfl
      have := congrArg Φ e2
      rw [map_mul, map_mul, hΦv₁, (MonoidHom.mem_ker.mp (hkerζ _ (hkerζ _ hh))),
        (MonoidHom.mem_ker.mp (hβH _ hh)), mul_one, mul_one, hΦv₀] at this
      exact hu₁u₀ this.symm
  intro v
  have hmem : Φ v ∈ Φ.range := ⟨v, rfl⟩
  rcases hall _ hmem with h | h | h | h
  · have hk : v ∈ Φ.ker := h
    rw [h]; exact (hβH _ hk)
  · obtain ⟨h₁, hh₁⟩ : ∃ h₁ : V, h₁ = v * v₀⁻¹ := ⟨_, rfl⟩
    have hhk : h₁ ∈ Φ.ker := by rw [hh₁]; exact hΦh v v₀ (by rw [h, hΦv₀])
    have e1 : v = h₁ * v₀ := by rw [hh₁, inv_mul_cancel_right]
    rw [e1, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hhk, MonoidHom.mem_ker.mp (hβH _ hhk),
      one_mul, one_mul, hkey, hΦv₀]
  · obtain ⟨h₁, hh₁⟩ : ∃ h₁ : V, h₁ = v * v₁⁻¹ := ⟨_, rfl⟩
    have hhk : h₁ ∈ Φ.ker := by rw [hh₁]; exact hΦh v v₁ (by rw [h, hΦv₁])
    have e1 : v = h₁ * v₁ := by rw [hh₁, inv_mul_cancel_right]
    rw [e1, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hhk, MonoidHom.mem_ker.mp (hβH _ hhk),
      one_mul, one_mul, hv₁, hβζ', hΦζ, hkey, hΦζ, hΦv₀]
  · obtain ⟨h₁, hh₁⟩ : ∃ h₁ : V, h₁ = v * v₂⁻¹ := ⟨_, rfl⟩
    have hhk : h₁ ∈ Φ.ker := by rw [hh₁]; exact hΦh v v₂ (by rw [h, hΦv₂])
    have e1 : v = h₁ * v₂ := by rw [hh₁, inv_mul_cancel_right]
    rw [e1, map_mul, map_mul, map_mul, MonoidHom.mem_ker.mp hhk, MonoidHom.mem_ker.mp (hβH _ hhk),
      one_mul, one_mul, hv₂, hv₁, hβζ', hβζ', hΦζ, hΦζ, hkey, hΦζ, hΦζ, hΦv₀]

end Helpers

section GenericCards

variable {G H : Type*} [Group G] [Group H]

theorem card_map_of_inf_ker_eq_bot (f : G →* H) {K : Subgroup G} (hK : K ⊓ f.ker = ⊥) :
    Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ f.ker := hx
    have h2 : (x : G) ∈ K ⊓ f.ker := ⟨x.2, h1⟩
    rw [hK] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h2))
  have hrange : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_inf_mul_index {V : Type*} [Group V] [Finite V] (hc : ∀ a b : V, a * b = b * a)
    {A K : Subgroup V} (hsup : A ⊔ K = ⊤) : Nat.card ↥(A ⊓ K) * K.index = Nat.card A := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  let ψ : ↥A →* V ⧸ K := (QuotientGroup.mk' K).comp A.subtype
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ A ⊔ K := hsup ▸ Subgroup.mem_top x
    obtain ⟨a, ha, k, hk, rfl⟩ := Subgroup.mem_sup.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk a = QuotientGroup.mk (a * k)
    rw [QuotientGroup.eq]
    simpa using K.inv_mem hk
  have h1 : ψ.ker.index = K.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj]
    simp [Subgroup.index]
  have h2 : ψ.ker = K.subgroupOf A := by
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have h3 : Nat.card ψ.ker * ψ.ker.index = Nat.card A := Subgroup.card_mul_index _
  rw [h1, h2] at h3
  have h4 : Nat.card (K.subgroupOf A) = Nat.card ↥(A ⊓ K) := by
    have h5 : Nat.card ↥(K ⊓ A) = Nat.card (K.subgroupOf A) := by
      rw [← Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective A)
    rw [inf_comm] at h5
    exact h5.symm
  rw [h4] at h3
  exact h3

end GenericCards

section Main

variable {Q V : Type} [Group Q] [Finite Q] [Group V] [Finite V] {θ : Q →* MulAut V}
  {J Y₀ : Subgroup Q}

theorem A6Setting.autFixSub_eq (S : A6Setting θ J Y₀) {a : Q} (ha : a ∈ J) (ha1 : a ≠ 1) :
    autFixSub (θ a) = fixQ θ J := by
  have hle : fixQ θ J ≤ autFixSub (θ a) := by
    intro v hv
    exact (mem_fixQ.mp hv) a ha
  exact (eq_of_le_of_index_eq hle (by rw [S.JC, S.Jidx a ha ha1])).symm

theorem stabComm_eq_top_of_nontrivial_center (S : A6Setting θ J Y₀) (hZ : Subgroup.center Q ≠ ⊥) :
    stabComm θ Y₀ = ⊤ := by
  classical
  obtain ⟨e₀⟩ := S.alt6
  have hc := S.hc
  have hV := S.hV
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := isSimpleGroup_of_alt6 e₀
  obtain ⟨a₀, ha₀J, ha₀1⟩ := S.exists_ne_one
  have hJnc : ¬ J ≤ Subgroup.center Q := by
    intro hJZ
    have h2 : orderOf a₀ = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact S.Jexp a₀ ha₀J) ha₀1
    have h3 : orderOf (⟨a₀, hJZ ha₀J⟩ : Subgroup.center Q) ∣ Nat.card (Subgroup.center Q) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h2] at h3
    exact (Nat.not_even_iff_odd.mpr S.odd) (even_iff_two_dvd.mpr h3)
  have hNC : Subgroup.normalClosure (J : Set Q) = ⊤ := normalClosure_eq_top S.perfect hsimple hJnc
  have hZ1 : Nat.card (Subgroup.center Q) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hpp, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card (Subgroup.center Q) :=
    ⟨_, Nat.minFac_prime hZ1, Nat.minFac_dvd _⟩
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpdvd
    exact (Nat.not_even_iff_odd.mpr S.odd) (even_iff_two_dvd.mpr hpdvd)
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) p hpdvd
  have hzc : (z' : Q) ∈ Subgroup.center Q := z'.2
  have hzo : orderOf (z' : Q) = p := by rw [Subgroup.orderOf_coe]; exact hz'
  set z : Q := (z' : Q) with hzdef
  set ζ : MulAut V := θ z with hζdef
  have hζp : ζ ^ p = 1 := by rw [hζdef, ← map_pow, ← hzo, pow_orderOf_eq_one, map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h
    have : z = 1 := S.faithful (by rw [← hζdef, h, map_one])
    rw [this, orderOf_one] at hzo
    exact hpp.one_lt.ne hzo
  have hcomm : ∀ k : Q, θ k * ζ = ζ * θ k := fun k => by
    rw [hζdef, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc k]
  have hcomm' : ∀ k : Q, ∀ v : V, θ k (ζ v) = ζ (θ k v) := fun k v => by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  have hrangeζ : ∀ k : Q, ∀ w ∈ autRange hc ζ, θ k w ∈ autRange hc ζ := by
    rintro k _ ⟨v, rfl⟩
    refine ⟨θ k v, ?_⟩
    rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcomm']
  have hnormK : (kerAct θ (autRange hc ζ)).Normal := kerAct_normal θ hrangeζ
  have hp3' : orderOf ζ ∣ p := orderOf_dvd_of_pow_eq_one hζp
  have hA' : ∀ a ∈ J, a ≠ 1 → (∀ u ∈ autRange hc (θ a), ζ u = u) → False := by
    intro a haJ ha1 htriv
    have hCa := S.autFixSub_eq haJ ha1
    have hzJ : ∀ v : V, ∀ a' ∈ J, θ a' (ζ v * v⁻¹) = ζ v * v⁻¹ := by
      intro v a' ha'
      have hΦeq : θ a (ζ v) * (ζ v)⁻¹ = θ a v * v⁻¹ := by
        have h2 := htriv (θ a v * v⁻¹) (autPhi_mem_autRange hc (θ a) v)
        rw [map_mul, map_inv, ← hcomm' a v] at h2
        exact h2
      have h1 : ζ v * v⁻¹ ∈ autFixSub (θ a) := by
        rw [← autPhi_ker hc (θ a), MonoidHom.mem_ker, map_mul, map_inv, autPhi_apply, autPhi_apply,
          hΦeq]
        exact mul_inv_cancel _
      rw [hCa] at h1
      exact (mem_fixQ.mp h1) a' ha'
    have hJK : J ≤ kerAct θ (autRange hc ζ) := by
      intro a' ha' w hw
      obtain ⟨v, rfl⟩ := hw
      exact hzJ v a' ha'
    have hNK : Subgroup.normalClosure (J : Set Q) ≤ kerAct θ (autRange hc ζ) :=
      Subgroup.normalClosure_le_normal hJK
    rw [hNC] at hNK
    have hzK : z ∈ kerAct θ (autRange hc ζ) := hNK (Subgroup.mem_top z)
    have h4 : ∀ v : V, ζ (ζ v) = v := by
      intro v
      have hk := (mem_kerAct.mp hzK) _ (autPhi_mem_autRange hc ζ v)
      rw [← hζdef, map_mul, map_inv] at hk
      let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
      have hsq : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
      have : ζ (ζ v) = ζ v * v⁻¹ * ζ v := by
        rw [← hk]; simp
      rw [this, hsq v]
      calc ζ v * v * ζ v = (ζ v * ζ v) * v := by ac_rfl
        _ = v := by rw [hV, one_mul]
    have hζ2 : ζ * ζ = 1 := MulEquiv.ext (fun v => by rw [MulAut.mul_apply, h4]; rfl)
    have hd2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hζ2)
    rcases (Nat.dvd_prime hpp).mp hp3' with h | h
    · exact hζ1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hd2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd2)
  have hp3 : p = 3 := by
    by_contra hne
    have h5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hne
    have hcard : Nat.card (autRange hc (θ a₀)) = 4 := by
      rw [card_autRange, S.Jidx a₀ ha₀J ha₀1]
    have hinv : ∀ u ∈ autRange hc (θ a₀), ζ u ∈ autRange hc (θ a₀) := by
      rintro _ ⟨v, rfl⟩
      refine ⟨ζ v, ?_⟩
      rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcomm']
    exact hA' a₀ ha₀J ha₀1 (fix_of_pow_prime_ge_five hcard hpp h5 hζp hinv)
  subst hp3
  have hζ3 : ζ ^ 3 = 1 := hζp
  have hinvℓ : ∀ a : Q, ∀ u ∈ autRange hc (θ a), ζ u ∈ autRange hc (θ a) := by
    rintro a _ ⟨v, rfl⟩
    refine ⟨ζ v, ?_⟩
    rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcomm' a v]
  have hcardℓ : ∀ a ∈ J, a ≠ 1 → Nat.card (autRange hc (θ a)) = 4 := by
    intro a ha ha1
    rw [card_autRange, S.Jidx a ha ha1]
  have hfpf : ∀ a ∈ J, a ≠ 1 → autRange hc (θ a) ⊓ autFixSub ζ = ⊥ := fun a ha ha1 =>
    fpf_of_nontrivial hc hV hζ3 (hcardℓ a ha ha1) (hinvℓ a) (by
      by_contra hno
      push Not at hno
      exact hA' a ha ha1 hno)
  have hℓV₀ : ∀ a ∈ J, a ≠ 1 → autRange hc (θ a) ≤ zV0 hc ζ := fun a ha ha1 =>
    le_zV0_of_fpf hc hζ3 (hinvℓ a) (hfpf a ha ha1)
  have hJV₁ : ∀ a ∈ J, ∀ v ∈ autFixSub ζ, θ a v = v := by
    intro a ha v hv
    by_cases ha1 : a = 1
    · rw [ha1, map_one]; rfl
    have hv' : ζ v = v := mem_autFixSub.mp hv
    have h1 : θ a v * v⁻¹ ∈ autRange hc (θ a) := autPhi_mem_autRange hc (θ a) v
    have h2 : θ a v * v⁻¹ ∈ autFixSub ζ := by
      rw [mem_autFixSub, map_mul, map_inv, hv', ← hcomm' a v, hv']
    have h3 : θ a v * v⁻¹ ∈ autRange hc (θ a) ⊓ autFixSub ζ := ⟨h1, h2⟩
    rw [hfpf a ha ha1] at h3
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)
  have hinvV₁ : ∀ k : Q, ∀ w ∈ autFixSub ζ, θ k w ∈ autFixSub ζ := by
    intro k w hw
    rw [mem_autFixSub, ← hcomm' k w, mem_autFixSub.mp hw]
  have hQV₁ : ∀ k : Q, ∀ v ∈ autFixSub ζ, θ k v = v := by
    have hnV₁ := kerAct_normal θ hinvV₁
    have hJK : J ≤ kerAct θ (autFixSub ζ) := fun a ha w hw => hJV₁ a ha w hw
    have hNK : Subgroup.normalClosure (J : Set Q) ≤ kerAct θ (autFixSub ζ) :=
      Subgroup.normalClosure_le_normal hJK
    rw [hNC] at hNK
    intro k v hv
    exact (mem_kerAct.mp (hNK (Subgroup.mem_top k))) v hv
  let fz : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hker : fz.ker = Subgroup.center Q := QuotientGroup.ker_mk' _
  have hoddker : Odd (Nat.card fz.ker) := by rw [hker]; exact S.odd
  have hkerle : fz.ker ≤ Subgroup.center Q := hker.le
  have hZsq : ∀ w ∈ Subgroup.center Q, w * w = 1 → w = 1 := by
    intro w hw hww
    have := CFSG.Alternating.Multipliers.eq_one_of_sq_eq_one_of_odd S.odd
      (k := (⟨w, hw⟩ : Subgroup.center Q)) (by apply Subtype.ext; simpa [pow_two] using hww)
    exact congrArg Subtype.val this
  have hJZ : J ⊓ Subgroup.center Q = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.mpr (hZsq a ha.2 (S.Jexp a ha.1))
  have hYZ : Y₀ ⊓ Subgroup.center Q = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgJ : g ∈ J := S.Ycent a₀ ha₀J ha₀1 g hg.1 (Subgroup.mem_center_iff.mp hg.2 a₀).symm
    have : g ∈ J ⊓ Subgroup.center Q := ⟨hgJ, hg.2⟩
    rw [hJZ] at this
    exact this
  have hfz1 : ∀ a ∈ J, a ≠ 1 → fz a ≠ 1 := by
    intro a ha ha1 h
    have h1 : a ∈ Subgroup.center Q := by rw [← hker]; exact h
    have h2 : a ∈ J ⊓ Subgroup.center Q := ⟨ha, h1⟩
    rw [hJZ] at h2
    exact ha1 (Subgroup.mem_bot.mp h2)
  have hJ4 : Nat.card (J.map fz) = 4 := by
    rw [card_map_of_inf_ker_eq_bot fz (by rw [hker]; exact hJZ)]
    exact S.Jcard
  have hJexp' : ∀ x ∈ J.map fz, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, S.Jexp a ha, map_one]
  obtain ⟨bb, hbbsq, hbbJ, hbbN, ⟨xx, hxxJ, hxxne⟩⟩ := alt6_klein_abs e₀ hJ4 hJexp'
  obtain ⟨b, hbbb, hbsq⟩ := CFSG.Alternating.Multipliers.exists_lift_sq_eq_one (f := fz) hkerle
    hoddker (MonoidHom.mem_range.mpr (QuotientGroup.mk'_surjective _ bb)) (by rw [pow_two]; exact hbbsq)
  have hb1 : b * b = 1 := by rw [← pow_two]; exact hbsq
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb1
  have hbbne : bb ≠ 1 := fun h => hbbJ (h ▸ (J.map fz).one_mem)
  have hb1' : b ≠ 1 := fun h => hbbne (by rw [← hbbb, h, map_one])
  have hbN : ∀ a ∈ J, b * a * b⁻¹ ∈ J := by
    intro a ha
    have h1 : fz (b * a * b⁻¹) = bb * fz a * bb⁻¹ := by rw [map_mul, map_mul, map_inv, hbbb]
    obtain ⟨a', ha'J, ha'eq⟩ := hbbN (fz a) ⟨a, ha, rfl⟩
    have h2 : fz a' = fz (b * a * b⁻¹) := by rw [h1]; exact ha'eq
    have h3 : a'⁻¹ * (b * a * b⁻¹) ∈ Subgroup.center Q := QuotientGroup.eq.mp h2
    set w := a'⁻¹ * (b * a * b⁻¹) with hw
    have h4 : b * a * b⁻¹ = a' * w := by rw [hw]; group
    have hsq1 : (b * a * b⁻¹) * (b * a * b⁻¹) = 1 := by
      calc (b * a * b⁻¹) * (b * a * b⁻¹) = b * (a * a) * b⁻¹ := by group
        _ = 1 := by rw [S.Jexp a ha]; group
    have hw1 : w = 1 := by
      apply hZsq w h3
      have h5 : (a' * w) * (a' * w) = a' * a' * (w * w) := by
        have := Subgroup.mem_center_iff.mp h3 a'
        calc a' * w * (a' * w) = a' * (w * a') * w := by group
          _ = a' * (a' * w) * w := by rw [← this]
          _ = a' * a' * (w * w) := by group
      rw [← h4, hsq1, S.Jexp a' ha'J, one_mul] at h5
      exact h5.symm
    rw [h4, hw1, mul_one]
    exact ha'J
  have hbmove : ∃ a ∈ J, b * a * b⁻¹ ≠ a := by
    obtain ⟨a, ha, rfl⟩ := hxxJ
    refine ⟨a, ha, fun h => hxxne ?_⟩
    have := congrArg fz h
    rw [map_mul, map_mul, map_inv, hbbb] at this
    exact this
  have hbJ' : fz b ∉ J.map fz := by rw [hbbb]; exact hbbJ
  have hbY : fz b ∉ Y₀.map fz := by
    rintro ⟨y, hyY, hyb⟩
    have h1 : y⁻¹ * b ∈ Subgroup.center Q := QuotientGroup.eq.mp hyb
    set w := y⁻¹ * b with hw
    have hby : b = y * w := by rw [hw]; group
    have hwc := Subgroup.mem_center_iff.mp h1
    have hy2 : y * y = 1 := by
      have hyw : y = b * w⁻¹ := by rw [hw]; group
      have hy2' : y * y ∈ Subgroup.center Q := by
        have : y * y = w⁻¹ * w⁻¹ := by
          calc y * y = b * w⁻¹ * (b * w⁻¹) := by rw [← hyw]
            _ = b * b * (w⁻¹ * w⁻¹) := by
              have hc' : w⁻¹ * b = b * w⁻¹ := by
                have := hwc b
                calc w⁻¹ * b = w⁻¹ * (b * w) * w⁻¹ := by group
                  _ = w⁻¹ * (w * b) * w⁻¹ := by rw [this]
                  _ = b * w⁻¹ := by group
              calc b * w⁻¹ * (b * w⁻¹) = b * (w⁻¹ * b) * w⁻¹ := by group
                _ = b * (b * w⁻¹) * w⁻¹ := by rw [hc']
                _ = b * b * (w⁻¹ * w⁻¹) := by group
            _ = w⁻¹ * w⁻¹ := by rw [hb1, one_mul]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ h1)
      have hy2'' : y * y ∈ Y₀ ⊓ Subgroup.center Q := ⟨Y₀.mul_mem hyY hyY, hy2'⟩
      rw [hYZ] at hy2''
      exact Subgroup.mem_bot.mp hy2''
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hyN' : ∀ a ∈ J, y * a * y⁻¹ ∈ J := by
      intro a ha
      have := hbN a ha
      have e : y * a * y⁻¹ = b * a * b⁻¹ := by
        have hwa : w * a * w⁻¹ = a := by
          calc w * a * w⁻¹ = (a * w) * w⁻¹ := by rw [← hwc a]
            _ = a := by group
        calc y * a * y⁻¹ = y * (w * a * w⁻¹) * y⁻¹ := by rw [hwa]
          _ = (y * w) * a * (y * w)⁻¹ := by group
          _ = b * a * b⁻¹ := by rw [← hby]
      rw [e]; exact this
    have hyN : y ∈ Subgroup.normalizer (J : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh; exact hyN' h hh
      · intro hh
        have := hyN' _ hh
        have e : y * (y * h * y⁻¹) * y⁻¹ = h := by
          calc y * (y * h * y⁻¹) * y⁻¹ = (y * y) * h * (y⁻¹ * y⁻¹) := by group
            _ = h := by rw [hy2, hyinv, hy2]; group
        rwa [e] at this
    have hyJ := mem_of_normalizes_two_group S.JY S.Y60 S.Jcard hyY hy2 hyN
    apply hbJ'
    rw [← hyb]
    exact ⟨y, hyJ, rfl⟩
  have hcardY : Nat.card (Y₀.map fz) = 60 := by
    rw [card_map_of_inf_ker_eq_bot fz (by rw [hker]; exact hYZ)]
    exact S.Y60
  have hsupfz : (Y₀.map fz) ⊔ Subgroup.zpowers (fz b) = ⊤ :=
    sup_zpowers_eq_top_of_card_sixty e₀ hcardY hbY
  have hQtop : Y₀ ⊔ Subgroup.zpowers b = ⊤ := by
    have hmap : (Y₀ ⊔ Subgroup.zpowers b).map fz = ⊤ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]; exact hsupfz
    have hsup2 : (Y₀ ⊔ Subgroup.zpowers b) ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq fz (Y₀ ⊔ Subgroup.zpowers b)
      rw [hmap, Subgroup.comap_top, hker] at this
      exact this.symm
    exact eq_top_of_sup_center S.perfect hsup2
  have hbidx : (autFixSub (θ b)).index = 4 := by
    obtain ⟨gg, hgg⟩ := alt6_involution_conj_abs e₀ (u := fz a₀) (v := bb)
      (by rw [← map_mul, S.Jexp a₀ ha₀J, map_one]) (hfz1 a₀ ha₀J ha₀1) hbbsq hbbne
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective _ gg
    have hconj : fz (g₁ * a₀ * g₁⁻¹) = fz b := by
      rw [map_mul, map_mul, map_inv, hbbb]; exact hgg
    have hsqc : (g₁ * a₀ * g₁⁻¹) ^ 2 = 1 := by
      calc (g₁ * a₀ * g₁⁻¹) ^ 2 = (g₁ * a₀ * g₁⁻¹) * (g₁ * a₀ * g₁⁻¹) := pow_two _
        _ = g₁ * (a₀ * a₀) * g₁⁻¹ := by group
        _ = 1 := by rw [S.Jexp a₀ ha₀J]; group
    have heq := CFSG.Alternating.Multipliers.eq_of_sq_eq_one hkerle hoddker hconj hsqc hbsq
    rw [← heq]
    exact S.index_conj ha₀J ha₀1
  obtain ⟨g, hgY, hgen⟩ := S.Ygen
  have hfixtop : fixQ θ ⊤ = (fixQ θ J ⊓ fixQ θ (J.map (MulAut.conj g).toMonoidHom)) ⊓
      fixQ θ (Subgroup.zpowers b) := by
    rw [← fixQ_sup, ← fixQ_sup, hgen, hQtop]
  have hidxtop : (fixQ θ ⊤).index ≤ 64 := by
    rw [hfixtop]
    have h1 : (fixQ θ J).index = 4 := S.JC
    have h2 : (fixQ θ (J.map (MulAut.conj g).toMonoidHom)).index = 4 := by
      rw [index_fixQ_conj, S.JC]
    have h3 : (fixQ θ (Subgroup.zpowers b)).index = 4 := by rw [fixQ_zpowers, hbidx]
    calc _ ≤ (fixQ θ J ⊓ fixQ θ (J.map (MulAut.conj g).toMonoidHom)).index *
          (fixQ θ (Subgroup.zpowers b)).index := Subgroup.index_inf_le
      _ ≤ ((fixQ θ J).index * (fixQ θ (J.map (MulAut.conj g).toMonoidHom)).index) *
          (fixQ θ (Subgroup.zpowers b)).index :=
        Nat.mul_le_mul_right _ Subgroup.index_inf_le
      _ = 64 := by rw [h1, h2, h3]
  have hCV₁ : fixQ θ ⊤ ≤ autFixSub ζ := fun v hv => (mem_fixQ.mp hv) z (Subgroup.mem_top z)
  have hV₀C : zV0 hc ζ ⊓ fixQ θ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h1 : v ∈ zV0 hc ζ ⊓ autFixSub ζ := ⟨hv.1, hCV₁ hv.2⟩
    rw [zV0_inf_fix hc hV] at h1
    exact h1
  have hV₀64 : Nat.card (zV0 hc ζ) ≤ 64 := (card_le_index_of_inf_eq_bot hV₀C).trans hidxtop
  have hV₁H : autFixSub ζ ≤ fixQ θ J := fun v hv => mem_fixQ.mpr (fun a ha => hJV₁ a ha v hv)
  have hV₀H : zV0 hc ζ ⊔ fixQ θ J = ⊤ := by
    rw [eq_top_iff, ← zV0_sup_fix hc hV hζ3]
    exact sup_le_sup_left hV₁H _
  have hcardH := card_inf_mul_index hc hV₀H
  rw [S.JC] at hcardH
  have hH16 : Nat.card ↥(zV0 hc ζ ⊓ fixQ θ J) ≤ 16 := by omega
  have hℓH : ∀ a ∈ J, autRange hc (θ a) ≤ fixQ θ J := by
    intro a ha
    rintro _ ⟨v, rfl⟩
    exact S.Jquad a ha v
  have hℓcomm : ∀ a ∈ J, autRange hc (θ a) ≤ commSub θ Y₀ := by
    intro a ha
    rintro _ ⟨v, rfl⟩
    exact mem_commSub_of_mem θ (S.JY ha) v
  have hV₀inv : ∀ k : Q, ∀ m ∈ zV0 hc ζ, θ k m ∈ zV0 hc ζ := by
    intro k m hm
    rw [mem_zV0] at hm ⊢
    have e1 : ζ (θ k m) = θ k (ζ m) := (hcomm' k m).symm
    have e2 : (ζ ^ 2) (θ k m) = θ k ((ζ ^ 2) m) := by
      rw [pow_two, MulAut.mul_apply, MulAut.mul_apply, e1, ← hcomm' k (ζ m)]
    rw [e1, e2, ← map_mul, ← map_mul, hm, map_one]
  have hθbζ : θ b * ζ = ζ * θ b := hcomm b
  have hθbb : θ b * θ b = 1 := by rw [← map_mul, hb1, map_one]
  have hθbH : ∀ h ∈ fixQ θ J, θ b h ∈ fixQ θ J := by
    intro h hh
    rw [mem_fixQ] at hh ⊢
    intro a' ha'
    have e : a' * b = b * (b * a' * b⁻¹) := by
      calc a' * b = (b * b) * a' * b := by rw [hb1, one_mul]
        _ = b * (b * a' * b⁻¹) := by rw [hbinv]; group
    have e2 : θ a' (θ b h) = θ b (θ (b * a' * b⁻¹) h) := by
      rw [← MulAut.mul_apply, ← map_mul, e, map_mul, MulAut.mul_apply]
    rw [e2, hh _ (hbN a' ha')]
  by_cases hroot : ∀ a₁ ∈ J, a₁ ≠ 1 → ∀ a₂ ∈ J, a₂ ≠ 1 → autRange hc (θ a₁) = autRange hc (θ a₂)
  ·
    exfalso
    obtain ⟨a, haJ, hmove⟩ := hbmove
    have ha1 : a ≠ 1 := fun h => hmove (by rw [h]; group)
    obtain ⟨a', ha'eq⟩ : ∃ a' : Q, a' = b * a * b⁻¹ := ⟨_, rfl⟩
    have ha'J : a' ∈ J := by rw [ha'eq]; exact hbN a haJ
    have ha'1 : a' ≠ 1 := by
      intro h
      apply ha1
      have : a = b⁻¹ * a' * b := by rw [ha'eq]; group
      rw [this, h]; group
    have hℓℓ : autRange hc (θ a') = autRange hc (θ a) := hroot a' ha'J ha'1 a haJ ha1
    have hcba : θ a * θ b = θ b * θ a' := by
      rw [← map_mul, ← map_mul]
      congr 1
      rw [ha'eq]
      calc a * b = a * b⁻¹ := by rw [hbinv]
        _ = (b * b) * a * b⁻¹ := by rw [hb1, one_mul]
        _ = b * (b * a * b⁻¹) := by group
    have hcba2 : θ a' * θ b = θ b * θ a := by
      rw [← map_mul, ← map_mul]
      congr 1
      rw [ha'eq]
      group
    have hcba' : ∀ v : V, θ a (θ b v) = θ b (θ a' v) := fun v => by
      have := congrArg (fun f : MulAut V => f v) hcba
      simpa [MulAut.mul_apply] using this
    have hcba2' : ∀ v : V, θ a' (θ b v) = θ b (θ a v) := fun v => by
      have := congrArg (fun f : MulAut V => f v) hcba2
      simpa [MulAut.mul_apply] using this
    have hbℓ : ∀ s ∈ autRange hc (θ a), θ b s ∈ autRange hc (θ a) := by
      rintro _ ⟨v, rfl⟩
      rw [← hℓℓ]
      refine ⟨θ b v, ?_⟩
      rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcba2' v]
    have hbtriv : ∀ s ∈ autRange hc (θ a), θ b s = s :=
      fix_of_commute_fpf hc hV hζ3 hθbζ hθbb (hcardℓ a haJ ha1) (hinvℓ a) hbℓ (hfpf a haJ ha1)
    have hker₁ : (autPhi hc (θ a)).ker = fixQ θ J := by
      rw [autPhi_ker, S.autFixSub_eq haJ ha1]
    have hΦζ : ∀ w : V, autPhi hc (θ a) (ζ w) = ζ (autPhi hc (θ a) w) := by
      intro w
      rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcomm' a w]
    have hmod := trivial_mod_ker hc hζ3 hθbζ hθbb (Φ := autPhi hc (θ a)) hΦζ
      (hcardℓ a haJ ha1) (hfpf a haJ ha1) (by
        intro h hh
        rw [hker₁] at hh ⊢
        exact hθbH h hh)
    have hΦeq : ∀ v : V, θ a' v * v⁻¹ = θ a v * v⁻¹ := by
      intro v
      have h1 : autPhi hc (θ a) (θ b v) = θ b (autPhi hc (θ a') v) := by
        rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcba' v]
      have h2 : θ b (autPhi hc (θ a') v) = autPhi hc (θ a') v := by
        refine hbtriv _ ?_
        rw [← hℓℓ]
        exact autPhi_mem_autRange hc (θ a') v
      calc θ a' v * v⁻¹ = autPhi hc (θ a') v := rfl
        _ = θ b (autPhi hc (θ a') v) := h2.symm
        _ = autPhi hc (θ a) (θ b v) := h1.symm
        _ = autPhi hc (θ a) v := hmod v
        _ = θ a v * v⁻¹ := rfl
    have hθeq : θ a' = θ a := MulEquiv.ext fun v => mul_right_cancel (hΦeq v)
    have haa : a' = a := S.faithful hθeq
    exact hmove (by rw [← ha'eq]; exact haa)
  ·
    push Not at hroot
    obtain ⟨a₁, ha₁J, ha₁1, a₂, ha₂J, ha₂1, hne⟩ := hroot
    have hge := card_sup_ge_sixteen hc hζ3 (hcardℓ a₁ ha₁J ha₁1) (hcardℓ a₂ ha₂J ha₂1)
      (hinvℓ a₁) (hinvℓ a₂) (hfpf a₁ ha₁J ha₁1) hne
    have hle : autRange hc (θ a₁) ⊔ autRange hc (θ a₂) ≤ zV0 hc ζ ⊓ fixQ θ J :=
      sup_le (le_inf (hℓV₀ a₁ ha₁J ha₁1) (hℓH a₁ ha₁J)) (le_inf (hℓV₀ a₂ ha₂J ha₂1) (hℓH a₂ ha₂J))
    have heq : autRange hc (θ a₁) ⊔ autRange hc (θ a₂) = zV0 hc ζ ⊓ fixQ θ J :=
      Subgroup.eq_of_le_of_card_ge hle (hH16.trans hge)
    have hbS : b ∈ stabComm θ Y₀ := by
      intro v
      have hker₁ : (autPhi hc (θ a₁)).ker = fixQ θ J := by
        rw [autPhi_ker, S.autFixSub_eq ha₁J ha₁1]
      have hΦζ : ∀ w : V, autPhi hc (θ a₁) (ζ w) = ζ (autPhi hc (θ a₁) w) := by
        intro w
        rw [autPhi_apply, autPhi_apply, map_mul, map_inv, hcomm' a₁ w]
      have hmod := trivial_mod_ker hc hζ3 hθbζ hθbb (Φ := autPhi hc (θ a₁)) hΦζ
        (hcardℓ a₁ ha₁J ha₁1) (hfpf a₁ ha₁J ha₁1) (by
          intro h hh
          rw [hker₁] at hh ⊢
          exact hθbH h hh) v
      have hH : θ b v * v⁻¹ ∈ fixQ θ J := by
        rw [← hker₁, MonoidHom.mem_ker, map_mul, map_inv, hmod]
        exact mul_inv_cancel _
      have hV₀' : θ b v * v⁻¹ ∈ zV0 hc ζ := by
        have hv : v ∈ zV0 hc ζ ⊔ autFixSub ζ := (zV0_sup_fix hc hV hζ3) ▸ Subgroup.mem_top v
        let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
        obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup.mp hv
        have e : θ b v * v⁻¹ = θ b m * m⁻¹ := by
          rw [← hmn, map_mul, hQV₁ b n hn]
          calc θ b m * n * (m * n)⁻¹ = θ b m * (n * n⁻¹) * m⁻¹ := by rw [mul_inv_rev]; group
            _ = θ b m * m⁻¹ := by rw [mul_inv_cancel, mul_one]
        rw [e]
        exact (zV0 hc ζ).mul_mem (hV₀inv b m hm) ((zV0 hc ζ).inv_mem hm)
      have hmem : θ b v * v⁻¹ ∈ autRange hc (θ a₁) ⊔ autRange hc (θ a₂) := by
        rw [heq]; exact ⟨hV₀', hH⟩
      exact (sup_le (hℓcomm a₁ ha₁J) (hℓcomm a₂ ha₂J)) hmem
    rw [eq_top_iff, ← hQtop]
    exact sup_le (le_stabComm θ Y₀) (Subgroup.zpowers_le.mpr hbS)

theorem stabComm_eq_top (S : A6Setting θ J Y₀) : stabComm θ Y₀ = ⊤ := by
  by_cases hZ : Subgroup.center Q = ⊥
  · exact stabComm_eq_top_of_trivial_center S hZ
  · exact stabComm_eq_top_of_nontrivial_center S hZ

end Main

end CFSG.CGT.PushingUpLit.CGT6
