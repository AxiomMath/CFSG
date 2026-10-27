module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Subgroup
open scoped commutatorElement

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_trivial_on_frattini_quotient_gen {r q : ℕ} [Fact r.Prime] [Fact q.Prime]
    {P : Subgroup G} (hPr : IsPGroup r P) (hrq : r ≠ q) {s : G}
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) (hs : IsPGroup q (zpowers s))
    (htriv : ∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ (frattini P).map P.subtype) :
    ∀ x ∈ P, s * x * s⁻¹ = x := by
  classical
  set A := zpowers s with hAdef
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (zpowers_le).2 hsP
  let α : A →* MulAut P := CFSG.Quasithin.A4.actionOn P A hAP
  have hα : ∀ (a : A) (y : P), ((α a y : P) : G) = (a : G) * y * (a : G)⁻¹ := fun _ _ => rfl
  set N := frattini P with hNdef
  have hN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    have h1 : N.map (α a).toMonoidHom ≤ N :=
      (characteristic_iff_map_le.1 inferInstance) _
    exact h1 ⟨n, hn, rfl⟩
  have hcop : ¬ q ∣ Nat.card N := by
    intro h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPr
    have h3 : q ∣ r ^ k := hk ▸ h2.trans (card_subgroup_dvd_card N)
    exact hrq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1
      (Nat.Prime.dvd_of_dvd_pow Fact.out h3)).symm
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting q hs α N hN hcop
  have hgen : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN
      ⟨s, mem_zpowers s⟩ = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, MulAut.one_apply,
        QuotientGroup.eq]
      obtain ⟨z, hz, hzy⟩ := htriv _ (y⁻¹).2
      have h1 : ((α ⟨s, mem_zpowers s⟩ y)⁻¹ * y : P) = z := by
        apply Subtype.ext
        have : (z : G) = s * ((y⁻¹ : P) : G) * s⁻¹ * ((y⁻¹ : P) : G)⁻¹ := hzy
        rw [this]
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hα]
        group
      rw [h1]
      exact hz
  have hall : ∀ a : A, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a =
      1 := by
    rintro ⟨_, n, rfl⟩
    have : (⟨s ^ n, n, rfl⟩ : A) = (⟨s, mem_zpowers s⟩ : A) ^ n := Subtype.ext (by simp)
    rw [this, map_zpow, hgen, one_zpow]
  set C : Subgroup P :=
    { carrier := {c | ∀ a : A, α a c = c}
      mul_mem' := fun {a b} ha hb x => by rw [map_mul, ha x, hb x]
      one_mem' := fun x => map_one _
      inv_mem' := fun {a} ha x => by rw [map_inv, ha x] } with hCdef
  have hCN : C ⊔ N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (y : P ⧸ N) ∈ {q : P ⧸ N | ∀ a : A,
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hN a q = q} :=
      fun a => by rw [hall a, MulAut.one_apply]
    rw [hlift] at hy
    obtain ⟨c, hc, hcy⟩ := hy
    have h1 : c⁻¹ * y ∈ N := QuotientGroup.eq.1 hcy
    have : y = c * (c⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left hc) (mem_sup_right h1)
  have hCtop : C = ⊤ := frattini_nongenerating hCN
  intro x hx
  have h1 : (⟨x, hx⟩ : P) ∈ C := hCtop ▸ mem_top _
  have h2 := congrArg Subtype.val (h1 ⟨s, mem_zpowers s⟩)
  rw [hα] at h2
  exact h2

end Burnside

section Phi

variable {G : Type*} [Group G]

@[expose] def phiG (Q : Subgroup G) : Subgroup G := (frattini Q).map Q.subtype

theorem phiG_le (Q : Subgroup G) : phiG Q ≤ Q := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem phiG_subgroupOf (Q : Subgroup G) : (phiG Q).subgroupOf Q = frattini Q :=
  Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _

theorem le_normalizer_phiG (Q : Subgroup G) : Q ≤ Subgroup.normalizer (phiG Q : Set G) := by
  have : ((phiG Q).subgroupOf Q).Normal := by
    rw [phiG_subgroupOf]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (phiG_le Q)).mp this

theorem conj_mem_phiG {Q : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) {a : G}
    (ha : a ∈ phiG Q) : n * a * n⁻¹ ∈ phiG Q := by
  obtain ⟨y, hy, rfl⟩ := ha
  let c : MulAut Q := CFSG.Quasithin.A4.actionOn Q (Subgroup.normalizer (Q : Set G)) le_rfl ⟨n, hn⟩
  have h1 : (frattini Q).map c.toMonoidHom ≤ frattini Q :=
    (characteristic_iff_map_le.1 inferInstance) c
  exact ⟨c y, h1 ⟨y, hy, rfl⟩, CFSG.Quasithin.A4.actionOn_apply_coe le_rfl ⟨n, hn⟩ y⟩

theorem comm_mem_phiG [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) : a * b * a⁻¹ * b⁻¹ ∈ phiG Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨⁅(⟨a, ha⟩ : Q), ⟨b, hb⟩⁆, CFSG.SectionRank.Ccomm.commutator_mem_frattini hQ _ _, by
    simp [commutatorElement_def]⟩

end Phi

theorem mem_normalizer_of_conj_mem_both {H : Type*} [Group H] {K : Subgroup H} {g : H}
    (h1 : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (h2 : ∀ k ∈ K, g⁻¹ * k * g ∈ K) :
    g ∈ Subgroup.normalizer (K : Set H) := by
  refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨h1 n, fun hn => ?_⟩
  have := h2 _ hn
  rwa [show g⁻¹ * (g * n * g⁻¹) * g = n by group] at this

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem perfect_acts_trivially_of_card_le_four {W₀ N H : Subgroup G}
    (hNn : (N.subgroupOf W₀).Normal) (hH : ⁅H, H⁆ = H)
    (hHW : H ≤ Subgroup.normalizer (W₀ : Set G)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hcard : Nat.card (↥W₀ ⧸ N.subgroupOf W₀) ≤ 4) :
    ∀ h ∈ H, ∀ w ∈ W₀, h * w * h⁻¹ * w⁻¹ ∈ N := by
  classical
  set N' := N.subgroupOf W₀ with hN'def
  let ψ₀ : H →* MulAut W₀ := CFSG.Quasithin.A4.actionOn W₀ H hHW
  have hψ₀ : ∀ (a : H) (n : W₀), ((ψ₀ a n : W₀) : G) = (a : G) * n * (a : G)⁻¹ := fun _ _ => rfl
  have hN' : ∀ a : H, ∀ n ∈ N', ψ₀ a n ∈ N' := by
    intro a n hn
    show ((ψ₀ a n : W₀) : G) ∈ N
    rw [hψ₀]
    exact (Subgroup.mem_normalizer_iff.mp (hHN a.2) _).mp hn
  let ψ : H →* MulAut (↥W₀ ⧸ N') :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction ψ₀ N' hN'
  have hsolv : Group.IsSolvable (MulAut (↥W₀ ⧸ N')) := by
    have h4 : Nat.card (↥W₀ ⧸ N') ≤ 4 := hcard
    have : Group.IsSolvable (Equiv.Perm (↥W₀ ⧸ N')) := Equiv.Perm.isSolvable h4
    exact Group.isSolvable_of_isSolvable_injective (f := (MulAut.toPerm (↥W₀ ⧸ N')))
      (fun a b hab => MulEquiv.ext fun x => by
        have := congrFun (congrArg (⇑) hab) x
        exact this)
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have htriv : ∀ a : H, ψ a = 1 := by
    intro a
    by_contra hne
    have : Nontrivial ψ.range :=
      ⟨⟨⟨ψ a, a, rfl⟩, 1, fun h => hne (by simpa using congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ψ.range) inferInstance
  intro h hh w hw
  have h1 := htriv ⟨h, hh⟩
  have h2 := congrArg (fun f : MulAut (↥W₀ ⧸ N') => f ((⟨w, hw⟩ : W₀) : ↥W₀ ⧸ N')) h1
  simp only [MulAut.one_apply] at h2
  rw [show ψ ⟨h, hh⟩ ((⟨w, hw⟩ : W₀) : ↥W₀ ⧸ N') = ((ψ₀ ⟨h, hh⟩ ⟨w, hw⟩ : W₀) : ↥W₀ ⧸ N')
    from rfl] at h2
  have h3 := QuotientGroup.eq_iff_div_mem.mp h2
  have h4 : ((ψ₀ ⟨h, hh⟩ ⟨w, hw⟩ / ⟨w, hw⟩ : W₀) : G) ∈ N := h3
  have h5 : ((ψ₀ ⟨h, hh⟩ ⟨w, hw⟩ / ⟨w, hw⟩ : W₀) : G) = h * w * h⁻¹ * w⁻¹ := by
    simp [div_eq_mul_inv, hψ₀]
  rwa [h5] at h4

end Perfect

section PieceA

variable {G : Type*} [Group G] [Finite G]

theorem comm_comm_mem_phiG {Q L V : Subgroup G} {x : G} (hQ : IsPGroup 2 Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hL : ⁅L, L⁆ = L) (hxL : x ∈ L)
    (hcent : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Q) (hV : Nat.card V ≤ 4)
    (hQV : ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ V) :
    ∀ q ∈ Q, x * (q * x * q⁻¹ * x⁻¹) * x⁻¹ * (q * x * q⁻¹ * x⁻¹)⁻¹ ∈ phiG Q := by
  classical
  let K : Subgroup G := Subgroup.closure {c | ∃ q ∈ Q, c = q * x * q⁻¹ * x⁻¹}
  have hKV : K ≤ V := (Subgroup.closure_le _).2 (by rintro _ ⟨q, hq, rfl⟩; exact hQV q hq)
  have hxQ : x ∈ Subgroup.normalizer (Q : Set G) := hLQ hxL
  have hcQ : ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ Q := fun q hq => by
    have h1 : x * q⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ _).mp (Q.inv_mem hq)
    have h2 := Q.mul_mem hq h1
    rwa [show q * (x * q⁻¹ * x⁻¹) = q * x * q⁻¹ * x⁻¹ by group] at h2
  have hKQ : K ≤ Q := (Subgroup.closure_le _).2 (by rintro _ ⟨q, hq, rfl⟩; exact hcQ q hq)
  have hcK : ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ K := fun q hq => Subgroup.subset_closure ⟨q, hq, rfl⟩
  set N := phiG Q with hNdef
  set W₀ := K ⊔ N with hW₀def
  have hKW : K ≤ W₀ := le_sup_left
  have hNW : N ≤ W₀ := le_sup_right
  have hW₀Q : W₀ ≤ Q := sup_le hKQ (phiG_le Q)
  have hNn : (N.subgroupOf W₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNW).mpr (hW₀Q.trans (le_normalizer_phiG Q))
  have hconj : ∀ l ∈ L, ∀ w ∈ W₀, l * w * l⁻¹ ∈ W₀ := by
    intro l hl w hw
    have hlN := hLQ hl
    have hmap : W₀.map (MulAut.conj l).toMonoidHom ≤ W₀ := by
      rw [hW₀def, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨q, hq, rfl⟩
        have ha : l * q * l⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hlN _).mp hq
        have hd : l * x * l⁻¹ * x⁻¹ ∈ Q := by
          have := Q.inv_mem (hcent l hl)
          rwa [show (x * l * x⁻¹ * l⁻¹)⁻¹ = l * x * l⁻¹ * x⁻¹ by group] at this
        have hb : x * (l * q * l⁻¹)⁻¹ * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxQ _).mp (Q.inv_mem ha)
        have he := comm_mem_phiG hQ (Q.inv_mem hb) hd
        have hid : l * (q * x * q⁻¹ * x⁻¹) * l⁻¹ =
            ((l * q * l⁻¹) * x * (l * q * l⁻¹)⁻¹ * x⁻¹) *
              ((x * (l * q * l⁻¹)⁻¹ * x⁻¹)⁻¹ * (l * x * l⁻¹ * x⁻¹) *
                (x * (l * q * l⁻¹)⁻¹ * x⁻¹)⁻¹⁻¹ * (l * x * l⁻¹ * x⁻¹)⁻¹) := by group
        show l * (q * x * q⁻¹ * x⁻¹) * l⁻¹ ∈ W₀
        rw [hid]
        exact W₀.mul_mem (hKW (hcK _ ha)) (hNW he)
      · rintro _ ⟨a, ha, rfl⟩
        exact hNW (conj_mem_phiG hlN ha)
    exact hmap ⟨w, hw, rfl⟩
  have hLW : L ≤ Subgroup.normalizer (W₀ : Set G) := fun l hl =>
    mem_normalizer_of_conj_mem_both (hconj l hl) (fun w hw => by simpa using hconj l⁻¹ (L.inv_mem hl) w hw)
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := fun l hl =>
    mem_normalizer_of_conj_mem_both (fun a ha => conj_mem_phiG (hLQ hl) ha)
      (fun a ha => by simpa using conj_mem_phiG (hLQ (L.inv_mem hl)) ha)
  have hcard : Nat.card (↥W₀ ⧸ N.subgroupOf W₀) ≤ 4 := by
    set π := QuotientGroup.mk' (N.subgroupOf W₀) with hπ
    have h1 : K.subgroupOf W₀ ⊔ N.subgroupOf W₀ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKW hNW]
      exact Subgroup.subgroupOf_self W₀
    have h2 : (K.subgroupOf W₀).map π = ⊤ := by
      have h3 := congrArg (Subgroup.map π) h1
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self (N.subgroupOf W₀), sup_bot_eq] at h3
      rw [h3, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (N.subgroupOf W₀))
    have hsurj : Function.Surjective (fun k : K.subgroupOf W₀ => π k) := by
      intro y
      have : y ∈ (K.subgroupOf W₀).map π := h2 ▸ Subgroup.mem_top y
      obtain ⟨k, hk, rfl⟩ := this
      exact ⟨⟨k, hk⟩, rfl⟩
    calc Nat.card (↥W₀ ⧸ N.subgroupOf W₀) ≤ Nat.card (K.subgroupOf W₀) :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKW).toEquiv
      _ ≤ Nat.card V := Subgroup.card_le_of_le hKV
      _ ≤ 4 := hV
  intro q hq
  exact perfect_acts_trivially_of_card_le_four hNn hL hLW hLN hcard x hxL _ (hKW (hcK q hq))

end PieceA

end CFSG.HardMathSupport.Cooperstein.StructureLie
