module

public import CFSG.GH74.GLS.IVK.Lifted.YModelOuter

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec7

section Product

variable {H : Type} [Group H]

theorem card_sup_mul_card_inf_of_commute {A B : Subgroup H} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_ker_mul_card_range (commProd A B hc)
  rw [range_commProd hc, Nat.card_prod] at h1
  have hker : Nat.card ↥(commProd A B hc).ker = Nat.card ↥(A ⊓ B) := by
    let toFun : ↥(commProd A B hc).ker → ↥(A ⊓ B) := fun p => ⟨(p.1.1 : H), p.1.1.2, by
      have h : (p.1.1 : H) * (p.1.2 : H) = 1 := by
        have h0 : commProd A B hc p.1 = 1 := p.2
        rwa [commProd_apply] at h0
      have : (p.1.1 : H) = (p.1.2 : H)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact B.inv_mem p.1.2.2⟩
    have hinj : Function.Injective toFun := by
      rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hp'⟩ h
      have h1' : (a : H) = a' := by
        have := congrArg Subtype.val h
        exact this
      have hab : (a : H) * (b : H) = 1 := by
        have h0 : commProd A B hc (a, b) = 1 := hp
        rwa [commProd_apply] at h0
      have hab' : (a' : H) * (b' : H) = 1 := by
        have h0 : commProd A B hc (a', b') = 1 := hp'
        rwa [commProd_apply] at h0
      have e1 : a = a' := Subtype.ext h1'
      have e2 : (b : H) = b' := by
        have hb : (b : H) = (a : H)⁻¹ := eq_inv_of_mul_eq_one_right hab
        have hb' : (b' : H) = (a' : H)⁻¹ := eq_inv_of_mul_eq_one_right hab'
        rw [hb, hb', h1']
      exact Subtype.ext (Prod.ext e1 (Subtype.ext e2))
    have hsurj : Function.Surjective toFun := by
      intro x
      refine ⟨⟨(⟨(x : H), x.2.1⟩, ⟨(x : H)⁻¹, B.inv_mem x.2.2⟩), ?_⟩, rfl⟩
      show commProd A B hc (⟨(x : H), x.2.1⟩, ⟨(x : H)⁻¹, B.inv_mem x.2.2⟩) = 1
      rw [commProd_apply]
      simp
    exact Nat.card_congr (Equiv.ofBijective toFun ⟨hinj, hsurj⟩)
  rw [hker] at h1
  rw [mul_comm]
  exact h1

theorem isSylowOf_sup_of_commute [Finite H] {E₁ E₂ P₁ P₂ : Subgroup H}
    (hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) (h₁ : IsSylowOf 2 P₁ E₁) (h₂ : IsSylowOf 2 P₂ E₂)
    (hinf : E₁ ⊓ E₂ ≤ P₁ ⊓ P₂) : IsSylowOf 2 (P₁ ⊔ P₂) (E₁ ⊔ E₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => hc a (h₁.le ha) b (h₂.le hb)
  have hinfeq : P₁ ⊓ P₂ = E₁ ⊓ E₂ :=
    le_antisymm (inf_le_inf h₁.le h₂.le) hinf
  have hcardP := card_sup_mul_card_inf_of_commute hcP
  have hcardE := card_sup_mul_card_inf_of_commute hc
  rw [hinfeq] at hcardP
  obtain ⟨a₁, ha₁⟩ := h₁.isPGroup.exists_card_eq
  obtain ⟨a₂, ha₂⟩ := h₂.isPGroup.exists_card_eq
  have hQ2 : IsPGroup 2 ↥(P₁ ⊔ P₂) := by
    have hdvd : Nat.card ↥(P₁ ⊔ P₂) ∣ 2 ^ (a₁ + a₂) := by
      refine Dvd.intro (Nat.card ↥(E₁ ⊓ E₂)) ?_
      rw [hcardP, ha₁, ha₂, pow_add]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hk
  rw [isSylowOf_iff] at h₁ h₂ ⊢
  refine ⟨sup_le_sup h₁.1 h₂.1, hQ2, ?_⟩
  have hr₁ := Subgroup.relIndex_mul_card (H := P₁) (K := E₁)
  have hr₂ := Subgroup.relIndex_mul_card (H := P₂) (K := E₂)
  have hr := Subgroup.relIndex_mul_card (H := P₁ ⊔ P₂) (K := E₁ ⊔ E₂)
  rw [inf_eq_left.2 h₁.1] at hr₁
  rw [inf_eq_left.2 h₂.1] at hr₂
  rw [inf_eq_left.2 (sup_le_sup h₁.1 h₂.1)] at hr
  have hdpos : 0 < Nat.card ↥(E₁ ⊓ E₂) := Nat.card_pos
  have hQpos : 0 < Nat.card ↥(P₁ ⊔ P₂) := Nat.card_pos
  have hmul : Nat.card ↥(P₁ ⊔ P₂) * (P₂.relIndex E₂ * P₁.relIndex E₁) * Nat.card ↥(E₁ ⊓ E₂) =
      Nat.card ↥(P₁ ⊔ P₂) * (P₁ ⊔ P₂).relIndex (E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) := by
    have e1 : Nat.card ↥(E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) = Nat.card ↥E₁ * Nat.card ↥E₂ := hcardE
    calc Nat.card ↥(P₁ ⊔ P₂) * (P₂.relIndex E₂ * P₁.relIndex E₁) * Nat.card ↥(E₁ ⊓ E₂) =
        (Nat.card ↥(P₁ ⊔ P₂) * Nat.card ↥(E₁ ⊓ E₂)) * (P₂.relIndex E₂ * P₁.relIndex E₁) := by ring
      _ = (Nat.card ↥P₁ * Nat.card ↥P₂) * (P₂.relIndex E₂ * P₁.relIndex E₁) := by rw [hcardP]
      _ = (P₁.relIndex E₁ * Nat.card ↥P₁) * (P₂.relIndex E₂ * Nat.card ↥P₂) := by ring
      _ = Nat.card ↥E₁ * Nat.card ↥E₂ := by rw [hr₁, hr₂]
      _ = Nat.card ↥(E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) := e1.symm
      _ = (P₁ ⊔ P₂).relIndex (E₁ ⊔ E₂) * Nat.card ↥(P₁ ⊔ P₂) * Nat.card ↥(E₁ ⊓ E₂) := by rw [hr]
      _ = Nat.card ↥(P₁ ⊔ P₂) * (P₁ ⊔ P₂).relIndex (E₁ ⊔ E₂) * Nat.card ↥(E₁ ⊓ E₂) := by ring
  have h2 := Nat.eq_of_mul_eq_mul_right hdpos hmul
  have h3 := Nat.eq_of_mul_eq_mul_left hQpos h2
  rw [← h3]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
  · exact h₂.2.2 h
  · exact h₁.2.2 h

end Product

section Model

variable {Gs : Type} [Group Gs]

theorem Ez_le_centralizer (z : Gs) : IVK.Ez z ≤ centralizer ({z} : Set Gs) :=
  Subgroup.map_subtype_le _

theorem centralizer_le_normalizer_Ez (z : Gs) :
    centralizer ({z} : Set Gs) ≤ normalizer (IVK.Ez z : Set Gs) := by
  have hn : ((IVK.Ez z).subgroupOf (centralizer ({z} : Set Gs))).Normal := by
    have : (IVK.Ez z).subgroupOf (centralizer ({z} : Set Gs)) = layer ↥(centralizer ({z} : Set Gs)) := by
      unfold IVK.Ez
      exact Subgroup.comap_map_eq_self_of_injective (centralizer ({z} : Set Gs)).subtype_injective
        (layer ↥(centralizer ({z} : Set Gs)))
    rw [this]
    have := CFSG.LocalCores.layer_characteristic (G := ↥(centralizer ({z} : Set Gs)))
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Ez_le_centralizer z)).1 hn

theorem isSylowOf_inf_factor [Finite Gs] {z : Gs} {S : Subgroup Gs} {Ei E : Subgroup Gs}
    (hS : IsSylowOf 2 S ⊤) (hSC : S ≤ centralizer ({z} : Set Gs)) (hE : E = IVK.Ez z) (hEi : Ei ≤ E)
    (hEiN : E ≤ normalizer (Ei : Set Gs)) : IsSylowOf 2 (S ⊓ Ei) Ei := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsSylowOf 2 S (centralizer ({z} : Set Gs)) := hS.of_le hSC le_top
  have hEC : E ≤ centralizer ({z} : Set Gs) := hE ▸ Ez_le_centralizer z
  have hCN : centralizer ({z} : Set Gs) ≤ normalizer (E : Set Gs) := hE ▸ centralizer_le_normalizer_Ez z
  have h2 : IsSylowOf 2 (S ⊓ E) E := h1.inf_of_le_normalizer hEC hCN
  have h3 : IsSylowOf 2 ((S ⊓ E) ⊓ Ei) Ei := h2.inf_of_le_normalizer hEi hEiN
  rwa [inf_assoc, inf_eq_right.2 hEi] at h3

theorem normalizer_of_commute {A B : Subgroup Gs} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ normalizer (A : Set Gs) :=
  sup_le Subgroup.le_normalizer
    (fun b hb => mem_normalizer_of_comm (fun n hn => (hc n hn b hb).symm))

theorem yconf_of_model [Finite Gs] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) {z' : Gs} {S' : Sylow 2 Gs} {t' w' : Gs} {E₁ E₂ : Subgroup Gs}
    (hz'2 : orderOf z' = 2)
    (hZS' : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z')
    (hdat : Dat410 (Nat.card F) z' (S' : Subgroup Gs) t' w' E₁ E₂)
    (e : ↥E₁ ≃* SpecialLinearGroup (Fin 2) F) :
    ∃ c : YConf F hodd h3 Gs, c.τ = t' ∧ c.ω = w' ∧ c.B = E₁ ⊔ E₂ ∧
      c.P = (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [hdat.t_ord, pow_two] at this
  have hω : w' * w' = 1 := by
    rcases hdat.w_ord with h | h
    · rw [h]
      simp
    · have := pow_orderOf_eq_one w'
      rwa [h, pow_two] at this
  have hz1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'2
    omega
  have htt : ∀ y : Gs, t' * (t' * y * t'⁻¹) * t'⁻¹ = y := fun y => by
    calc t' * (t' * y * t'⁻¹) * t'⁻¹ = (t' * t') * y * (t' * t')⁻¹ := by group
      _ = y := by rw [hτ]; group
  have hsw : swapSub E₁ t' = E₂ := by
    ext x
    rw [hdat.E₂_eq, mem_swapSub, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨t' * x * t'⁻¹, hx, htt x⟩
    · rintro ⟨y, hy, rfl⟩
      show t' * (t' * y * t'⁻¹) * t'⁻¹ ∈ E₁
      rw [htt y]
      exact hy
  have hz'S : z' ∈ (S' : Subgroup Gs) := by
    have : z' ∈ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype := by
      rw [hZS']
      exact mem_zpowers z'
    obtain ⟨y, -, hy⟩ := this
    rw [← hy]
    exact y.2
  have hS'C : (S' : Subgroup Gs) ≤ centralizer ({z'} : Set Gs) := by
    intro s hs
    have : z' ∈ (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype := by
      rw [hZS']
      exact mem_zpowers z'
    obtain ⟨y, hy, hyz⟩ := this
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_center_iff.1 hy ⟨s, hs⟩
    have h2 : s * (y : Gs) = (y : Gs) * s := congrArg Subtype.val h1
    rw [← hyz]
    exact h2.symm.symm
  have hS'syl : IsSylowOf 2 (S' : Subgroup Gs) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, S'.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S'.not_dvd_index
  have hE : E₁ ⊔ E₂ = IVK.Ez z' := hdat.Ez_eq.symm
  have hc₂ : ∀ a ∈ E₂, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb => (hdat.comm_E b hb a ha).symm
  have hsyl₁ : IsSylowOf 2 ((S' : Subgroup Gs) ⊓ E₁) E₁ :=
    isSylowOf_inf_factor hS'syl hS'C hE le_sup_left (normalizer_of_commute hdat.comm_E)
  have hsyl₂ : IsSylowOf 2 ((S' : Subgroup Gs) ⊓ E₂) E₂ :=
    isSylowOf_inf_factor hS'syl hS'C hE le_sup_right
      (by rw [sup_comm]; exact normalizer_of_commute hc₂)
  have hinf : E₁ ⊓ E₂ ≤ ((S' : Subgroup Gs) ⊓ E₁) ⊓ ((S' : Subgroup Gs) ⊓ E₂) := by
    intro x hx
    have hxz : x ∈ zpowers z' := by
      rw [← hdat.inter_E]
      exact hx
    have hxS : x ∈ (S' : Subgroup Gs) := (zpowers_le.2 hz'S) hxz
    exact ⟨⟨hxS, hx.1⟩, ⟨hxS, hx.2⟩⟩
  have hsylE := isSylowOf_sup_of_commute hdat.comm_E hsyl₁ hsyl₂ hinf
  have hSE : (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂) = ((S' : Subgroup Gs) ⊓ E₁) ⊔ ((S' : Subgroup Gs) ⊓ E₂) := by
    have h0 : IsSylowOf 2 ((S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂)) (E₁ ⊔ E₂) :=
      isSylowOf_inf_factor hS'syl hS'C hE le_rfl Subgroup.le_normalizer
    have hle : ((S' : Subgroup Gs) ⊓ E₁) ⊔ ((S' : Subgroup Gs) ⊓ E₂) ≤ (S' : Subgroup Gs) ⊓ (E₁ ⊔ E₂) :=
      sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    exact hsylE.eq_of_le hle inf_le_right h0.isPGroup
  have hswP : swapSub ((S' : Subgroup Gs) ⊓ E₁) t' = (S' : Subgroup Gs) ⊓ E₂ := by
    ext x
    rw [mem_swapSub]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, hsw ▸ (mem_swapSub.2 h2)⟩
      have h3' := (S' : Subgroup Gs).mul_mem
        ((S' : Subgroup Gs).mul_mem ((S' : Subgroup Gs).inv_mem hdat.t_mem) h1) hdat.t_mem
      have e : t'⁻¹ * (t' * x * t'⁻¹) * t' = x := by group
      rw [e] at h3'
      exact h3'
    · rintro ⟨h1, h2⟩
      have h2' : x ∈ swapSub E₁ t' := hsw.symm ▸ h2
      exact ⟨(S' : Subgroup Gs).mul_mem ((S' : Subgroup Gs).mul_mem hdat.t_mem h1)
        ((S' : Subgroup Gs).inv_mem hdat.t_mem), mem_swapSub.1 h2'⟩
  have hwN : w' ∈ normalizer (E₁ : Set Gs) := by
    have : w' ∈ normalizer (E₁ : Set Gs) ⊓ (S' : Subgroup Gs) := by
      rw [hdat.norm_E]
      exact mem_sup_right (mem_zpowers w')
    exact this.1
  have hout : w' ≠ 1 → TwoThin.conjAut hwN ∉ innOf ↥E₁ ∧
      (gammaOf hodd h3 (MulAut.congr e (TwoThin.conjAut hwN))).right = 1 := by
    intro hw1
    obtain ⟨hn, hPGL⟩ := hdat.pgl hw1 E₁ (Set.mem_insert _ _)
    obtain ⟨Q, hQ⟩ := hsyl₁.exists_sylow_eq_subgroupOf
    have hz₁ : z' ∈ E₁ := by
      have : z' ∈ E₁ ⊓ E₂ := by
        rw [hdat.inter_E]
        exact mem_zpowers z'
      exact this.1
    have hzc : ∀ a ∈ E₁, a * z' = z' * a := by
      have : z' ∈ E₁ ⊓ E₂ := by
        rw [hdat.inter_E]
        exact mem_zpowers z'
      exact fun a ha => hdat.comm_E a ha z' this.2
    refine model_outer hodd h3 e hz₁ hzc hz1 hwN hω hn hPGL Q (fun x hx => ?_)
    have hx' : (x : Gs) ∈ (S' : Subgroup Gs) ⊓ E₁ := by
      have : x ∈ (Q : Subgroup ↥E₁) := hx
      rw [hQ] at this
      exact this
    have : ((TwoThin.conjAut hwN x : ↥E₁) : Gs) ∈ (S' : Subgroup Gs) ⊓ E₁ := by
      refine ⟨?_, ?_⟩
      · exact (S' : Subgroup Gs).mul_mem ((S' : Subgroup Gs).mul_mem hdat.w_mem hx'.1)
          ((S' : Subgroup Gs).inv_mem hdat.w_mem)
      · exact (TwoThin.conjAut hwN x).2
    show TwoThin.conjAut hwN x ∈ (Q : Subgroup ↥E₁)
    rw [hQ]
    exact this
  have hz₁₂ : z' ∈ E₁ ⊓ E₂ := by
    rw [hdat.inter_E]
    exact mem_zpowers z'
  have hcomm' : ∀ a ∈ E₁, ∀ b ∈ swapSub E₁ t', a * b = b * a := fun a ha b hb =>
    hdat.comm_E a ha b (hsw ▸ hb)
  have hz₂ : z' ∈ swapSub E₁ t' := by
    rw [hsw]
    exact hz₁₂.2
  have hωP : ∀ x ∈ (S' : Subgroup Gs) ⊓ E₁, w' * x * w'⁻¹ ∈ (S' : Subgroup Gs) ⊓ E₁ := fun x hx =>
    ⟨(S' : Subgroup Gs).mul_mem ((S' : Subgroup Gs).mul_mem hdat.w_mem hx.1)
      ((S' : Subgroup Gs).inv_mem hdat.w_mem), (Subgroup.mem_normalizer_iff.1 hwN x).1 hx.2⟩
  have hBY : (E₁ ⊔ swapSub E₁ t') ⊓ (zpowers t' ⊔ zpowers w') = ⊥ := by
    rw [hsw, hE]
    exact hdat.inter
  refine ⟨⟨E₁, (S' : Subgroup Gs) ⊓ E₁, t', w', z', e, TwoThin.conjAut hwN, hτ, hω, hdat.comm,
    fun a => rfl, hcomm', hz₁₂.1, hz₂, fun a ha => hdat.comm_E a ha z' hz₁₂.2, hz1, hsyl₁, hωP, hBY,
    hout⟩, rfl, rfl, ?_, ?_⟩
  · show E₁ ⊔ swapSub E₁ t' = E₁ ⊔ E₂
    rw [hsw]
  · show ((S' : Subgroup Gs) ⊓ E₁) ⊔ swapSub ((S' : Subgroup Gs) ⊓ E₁) t' = _
    rw [hswP, hSE]

end Model

end CFSG.GH74.GLS.IVK.Lifted
