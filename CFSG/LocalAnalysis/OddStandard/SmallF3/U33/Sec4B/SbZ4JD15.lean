module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD14
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD5

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem range_card_index {N α : Type*} [Group N] (K : Subgroup N) (f : N → α)
    (hf : ∀ n m : N, f n = f m ↔ n⁻¹ * m ∈ K) : Nat.card (Set.range f) = K.index := by
  let g : N ⧸ K → α := Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((hf _ _).mp hab)
  have hrange : Set.range f = Set.range g := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H n => exact ⟨n, rfl⟩
  rw [hrange, Nat.card_range_of_injective hg]
  rfl

private theorem conj_eq_iff_comm {G : Type*} [Group G] (w a : G) :
    w * a * w⁻¹ = a ↔ w * a = a * w := by
  constructor
  · intro h
    have h' := congrArg (fun x => x * w) h
    simpa [mul_assoc] using h'
  · intro h; rw [h]; group

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem exists_conj_Y {α : H} (hα : α ∈ Mc) (hαQ : α ∉ Q) {v : H} (hv : v ∈ V) :
    ∃ u ∈ Y, u * α * u⁻¹ = α * v := by
  have hαMh : α ∈ Mh := Mc_le_Mh h hMh hMc hα
  have hαE : α ∉ centralizer (Y : Set H) :=
    fun hc => hαQ (mem_Q_of_mem_Mc_cent_Y h hMh hMc hα hc)
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  let f : Y → H := fun u => (u : H) * α * (u : H)⁻¹
  have hf : ∀ u u' : Y, f u = f u' ↔ u⁻¹ * u' ∈ V.subgroupOf Y := by
    intro u u'
    set w : H := (u : H)⁻¹ * (u' : H) with hwdef
    have hwY : w ∈ Y := by
      rw [hwdef]
      exact Y.mul_mem (Y.inv_mem u.2) u'.2
    have hcoe : ((u⁻¹ * u' : Y) : H) = w := by rw [hwdef]; rfl
    rw [Subgroup.mem_subgroupOf, hcoe]
    have hconj : f u = f u' ↔ w * α * w⁻¹ = α := by
      have hu'w : (u' : H) = (u : H) * w := by rw [hwdef]; group
      constructor
      · intro hh
        change (u : H) * α * (u : H)⁻¹ = (u' : H) * α * (u' : H)⁻¹ at hh
        rw [hu'w] at hh
        have h2 : (u : H) * (α * (u : H)⁻¹) =
            (u : H) * ((w * α * w⁻¹) * (u : H)⁻¹) := by
          rw [show (u : H) * α * (u : H)⁻¹ = (u : H) * (α * (u : H)⁻¹) by group,
              show ((u : H) * w) * α * ((u : H) * w)⁻¹ =
                (u : H) * ((w * α * w⁻¹) * (u : H)⁻¹) by group] at hh
          exact hh
        exact (mul_right_cancel (mul_left_cancel h2)).symm
      · intro hh
        change (u : H) * α * (u : H)⁻¹ = (u' : H) * α * (u' : H)⁻¹
        rw [hu'w]
        rw [show ((u : H) * w) * α * ((u : H) * w)⁻¹ =
            (u : H) * (w * α * w⁻¹) * (u : H)⁻¹ by group, hh]
    have hcomm : w * α * w⁻¹ = α ↔ w * α = α * w := conj_eq_iff_comm w α
    have hViff : w * α = α * w ↔ w ∈ V := by
      constructor
      · intro hc
        refine Mh_cent_Y h hMh hαMh hαE hwY ?_
        rw [← hc]; group
      · intro hwV
        have hc := Mh_cent_V h hMh hαMh hwV
        calc w * α = (α * w * α⁻¹) * α := by rw [hc]
          _ = α * w := by group
    exact hconj.trans (hcomm.trans hViff)
  have hrange : Nat.card (Set.range f) = 4 := by
    rw [range_card_index (V.subgroupOf Y) f hf]
    have hVcard : Nat.card ↥(V.subgroupOf Y) = 4 := by
      have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVY).toEquiv
      rw [hc]; exact h.card_V
    have hmul := Subgroup.index_mul_card (V.subgroupOf Y)
    rw [hVcard, card_Y h] at hmul
    omega
  have hcommV : ∀ u : Y, (u : H) * α * (u : H)⁻¹ * α⁻¹ ∈ V := by
    intro u
    have h1 : α * (u : H) * α⁻¹ * (u : H)⁻¹ ∈ V :=
      Mh_comm_Q h hMh hαMh (h.Y_le_Q u.2)
    have h2 : (α * (u : H) * α⁻¹ * (u : H)⁻¹)⁻¹ =
        (u : H) * α * (u : H)⁻¹ * α⁻¹ := by group
    rw [← h2]
    exact V.inv_mem h1
  have hkey : ∀ u : Y, f u = α * ((u : H) * α * (u : H)⁻¹ * α⁻¹) := by
    intro u
    have hcent := Mh_cent_V h hMh hαMh (hcommV u)
    calc f u = ((u : H) * α * (u : H)⁻¹ * α⁻¹) * α := by
          change (u : H) * α * (u : H)⁻¹ =
            ((u : H) * α * (u : H)⁻¹ * α⁻¹) * α
          group
      _ = α * ((u : H) * α * (u : H)⁻¹ * α⁻¹) := by
          have h' := congrArg (fun y => y * α) hcent
          rw [← h']
          group
  let g : V → H := fun w => α * (w : H)
  have hginj : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (mul_left_cancel hab)
  have hTcard : Nat.card (Set.range g) = 4 := by
    rw [Nat.card_range_of_injective hginj, h.card_V]
  have hsub : Set.range f ⊆ Set.range g := by
    rintro x ⟨u, rfl⟩
    exact ⟨⟨(u : H) * α * (u : H)⁻¹ * α⁻¹, hcommV u⟩, (hkey u).symm⟩
  have hg4 : (Set.range g).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, hTcard]
  have hf4 : (Set.range f).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, hrange]
  have hseteq : Set.range f = Set.range g :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hg4, hf4])
  have hmem : α * v ∈ Set.range f := by
    rw [hseteq]
    exact ⟨⟨v, hv⟩, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, u.2, hu⟩

theorem exists_conj_Mc {w : H} (hw : w ∈ Y) (hwV : w ∉ V) {v : H} (hv : v ∈ V) :
    ∃ m ∈ Mc, m * w * m⁻¹ = w * v := by
  have hwMc : w ∈ Mc := Q_le_Mc h hMh hMc (h.Y_le_Q hw)
  have hwQ : w ∈ Q := h.Y_le_Q hw
  let f : Mc → H := fun m => (m : H) * w * (m : H)⁻¹
  let K : Subgroup Mc := (Mc ⊓ centralizer ({w} : Set H)).subgroupOf Mc
  have hf : ∀ m m' : Mc, f m = f m' ↔ m⁻¹ * m' ∈ K := by
    intro m m'
    set w' : H := (m : H)⁻¹ * (m' : H) with hw'def
    have hcoe : ((m⁻¹ * m' : Mc) : H) = w' := by rw [hw'def]; rfl
    have hmemMc : ((m⁻¹ * m' : Mc) : H) ∈ Mc := (m⁻¹ * m').2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hcoe]
    have hconj : f m = f m' ↔ w' * w * w'⁻¹ = w := by
      have hm'w : (m' : H) = (m : H) * w' := by rw [hw'def]; group
      constructor
      · intro hh
        change (m : H) * w * (m : H)⁻¹ = (m' : H) * w * (m' : H)⁻¹ at hh
        rw [hm'w] at hh
        have h2 : (m : H) * (w * (m : H)⁻¹) =
            (m : H) * ((w' * w * w'⁻¹) * (m : H)⁻¹) := by
          rw [show (m : H) * w * (m : H)⁻¹ = (m : H) * (w * (m : H)⁻¹) by group,
              show ((m : H) * w') * w * ((m : H) * w')⁻¹ =
                (m : H) * ((w' * w * w'⁻¹) * (m : H)⁻¹) by group] at hh
          exact hh
        exact (mul_right_cancel (mul_left_cancel h2)).symm
      · intro hh
        change (m : H) * w * (m : H)⁻¹ = (m' : H) * w * (m' : H)⁻¹
        rw [hm'w]
        rw [show ((m : H) * w') * w * ((m : H) * w')⁻¹ =
            (m : H) * (w' * w * w'⁻¹) * (m : H)⁻¹ by group, hh]
    have hcent : w' * w * w'⁻¹ = w ↔ w' ∈ centralizer ({w} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact conj_eq_iff_comm w' w
    constructor
    · intro hh
      exact ⟨hmemMc, (hconj.trans hcent).mp hh⟩
    · rintro ⟨-, hc⟩
      exact (hconj.trans hcent).mpr hc
  have hKQ : Mc ⊓ centralizer ({w} : Set H) ≤ Q := by
    intro m hm
    obtain ⟨hmMc, hmC⟩ := Subgroup.mem_inf.mp hm
    by_contra hmQ
    have hmMh : m ∈ Mh := Mc_le_Mh h hMh hMc hmMc
    have hmE : m ∉ centralizer (Y : Set H) :=
      fun hc => hmQ (mem_Q_of_mem_Mc_cent_Y h hMh hMc hmMc hc)
    have hc : m * w * m⁻¹ = w := by
      have hcm : m * w = w * m := Subgroup.mem_centralizer_singleton_iff.mp hmC
      rw [hcm]; group
    exact hwV (Mh_cent_Y h hMh hmMh hmE hw hc)
  have hKcard : Nat.card K ≤ 64 := by
    have heq : Nat.card K = Nat.card ↥(Mc ⊓ centralizer ({w} : Set H)) := by
      have hle : Mc ⊓ centralizer ({w} : Set H) ≤ Mc := inf_le_left
      have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      exact hc
    rw [heq]
    calc Nat.card ↥(Mc ⊓ centralizer ({w} : Set H)) ≤ Nat.card Q :=
          Subgroup.card_le_of_le hKQ
      _ = 64 := h.card_Q
  have hidx : 4 ≤ K.index := by
    have hmul := Subgroup.index_mul_card K
    rw [card_Mc h hMh hMc] at hmul
    by_contra hlt
    have hle3 : K.index ≤ 3 := by omega
    have hle := Nat.mul_le_mul hle3 hKcard
    omega
  have hrange : Nat.card (Set.range f) = K.index := range_card_index K f hf
  have hVQ : V ≤ Q := by
    intro x hx
    exact h.Y_le_Q (by rw [h.Y_eq]; exact Subgroup.mem_sup_left hx)
  have hcommV : ∀ m : Mc, (m : H) * w * (m : H)⁻¹ * w⁻¹ ∈ V := by
    intro m
    exact Mh_comm_Q h hMh (Mc_le_Mh h hMh hMc m.2) hwQ
  have hkey : ∀ m : Mc, f m = w * ((m : H) * w * (m : H)⁻¹ * w⁻¹) := by
    intro m
    calc f m = ((m : H) * w * (m : H)⁻¹ * w⁻¹) * w := by
          change (m : H) * w * (m : H)⁻¹ =
            ((m : H) * w * (m : H)⁻¹ * w⁻¹) * w
          group
      _ = w * ((m : H) * w * (m : H)⁻¹ * w⁻¹) := by
          rw [h.Q_comm _ (hVQ (hcommV m)) w hwQ]
  let g : V → H := fun x => w * (x : H)
  have hginj : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (mul_left_cancel hab)
  have hTcard : Nat.card (Set.range g) = 4 := by
    rw [Nat.card_range_of_injective hginj, h.card_V]
  have hsub : Set.range f ⊆ Set.range g := by
    rintro x ⟨m, rfl⟩
    exact ⟨⟨(m : H) * w * (m : H)⁻¹ * w⁻¹, hcommV m⟩, (hkey m).symm⟩
  have hf_ncard : (Set.range f).ncard = K.index := by
    rw [← Nat.card_coe_set_eq, hrange]
  have hg_ncard : (Set.range g).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, hTcard]
  have hle4 : K.index ≤ 4 := by
    calc K.index = (Set.range f).ncard := hf_ncard.symm
      _ ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub
      _ = 4 := hg_ncard
  have hidx4 : K.index = 4 := le_antisymm hle4 hidx
  have hseteq : Set.range f = Set.range g :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hg_ncard, hf_ncard, hidx4])
  have hmem : w * v ∈ Set.range f := by
    rw [hseteq]
    exact ⟨⟨v, hv⟩, rfl⟩
  obtain ⟨m, hm⟩ := hmem
  exact ⟨m, m.2, hm⟩

theorem cent_V_Vh : zjVh Mc t τ l ⊓ centralizer (V : Set H) = Mc ⊔ closure ({t, τ} : Set H) := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hMcCentV : Mc ≤ centralizer (V : Set H) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hh := Mh_cent_V h hMh (Mc_le_Mh h hMh hMc hm) hv
    calc v * m = (m * v * m⁻¹) * m := by rw [hh]
      _ = m * v := by group
  have htCentV : t ∈ centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (h.V_cent_t v hv).symm
  have htauCentV : τ ∈ centralizer (V : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvY : v ∈ Y := hVY hv
    have hvQ : v ∈ Q := h.Y_le_Q hvY
    have hvv : v * v = 1 := h.Y_sq v hvY
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    have ht := h.tau_inv v hvQ
    calc v * τ = (τ * v * τ⁻¹) * τ := by rw [ht, hvinv]
      _ = τ * v := by group
  have hlCentV : l ∉ centralizer (V : Set H) := by
    intro hl
    have hy : y ∈ V := by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)
    have hcomm : y * l = l * y := (Subgroup.mem_centralizer_iff.mp hl) y hy
    have hyl : l * y * l⁻¹ = y := by rw [← hcomm]; group
    have hyz : y = y * z := hyl.symm.trans h.l_y
    have hz : z = 1 := by
      have h1 : y * (1 : H) = y * z := by rw [mul_one]; exact hyz
      exact (mul_left_cancel h1).symm
    exact h.z_ne_one hz
  apply le_antisymm
  · intro g hg
    obtain ⟨hgVh, hgC⟩ := Subgroup.mem_inf.mp hg
    rcases (mem_Vh_iff h hMh hMc).mp hgVh with
      ⟨m, hm, h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1⟩
    · rw [h1]; exact Subgroup.mem_sup_left hm
    · rw [h1]
      refine mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ?_)
      exact Subgroup.subset_closure (by simp)
    · rw [h1]
      refine mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ?_)
      exact Subgroup.subset_closure (by simp)
    · rw [h1]
      refine mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right ?_)
      exact mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · have hmC : m ∈ centralizer (V : Set H) := hMcCentV hm
      have hgm : m⁻¹ * g ∈ centralizer (V : Set H) :=
        mul_mem (Subgroup.inv_mem _ hmC) hgC
      have hkey : m⁻¹ * g = l := by rw [h1]; group
      rw [hkey] at hgm
      exact absurd hgm hlCentV
    · have hmC : m * t ∈ centralizer (V : Set H) :=
        mul_mem (hMcCentV hm) htCentV
      have hgm : (m * t)⁻¹ * g ∈ centralizer (V : Set H) :=
        mul_mem (Subgroup.inv_mem _ hmC) hgC
      have hkey : (m * t)⁻¹ * g = l := by rw [h1]; group
      rw [hkey] at hgm
      exact absurd hgm hlCentV
    · have hmC : m * τ ∈ centralizer (V : Set H) :=
        mul_mem (hMcCentV hm) htauCentV
      have hgm : (m * τ)⁻¹ * g ∈ centralizer (V : Set H) :=
        mul_mem (Subgroup.inv_mem _ hmC) hgC
      have hkey : (m * τ)⁻¹ * g = l := by rw [h1]; group
      rw [hkey] at hgm
      exact absurd hgm hlCentV
    · have hmC : m * (t * τ) ∈ centralizer (V : Set H) :=
        mul_mem (hMcCentV hm) (mul_mem htCentV htauCentV)
      have hgm : (m * (t * τ))⁻¹ * g ∈ centralizer (V : Set H) :=
        mul_mem (Subgroup.inv_mem _ hmC) hgC
      have hkey : (m * (t * τ))⁻¹ * g = l := by rw [h1]; group
      rw [hkey] at hgm
      exact absurd hgm hlCentV
  · refine sup_le ?_ ?_
    · exact le_inf (Mc_le_zjVh Mc t τ l) hMcCentV
    · rw [Subgroup.closure_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxt | hxτ
      · rw [hxt]; exact Subgroup.mem_inf.mpr ⟨t_mem_zjVh Mc t τ l, htCentV⟩
      · rw [hxτ]; exact Subgroup.mem_inf.mpr ⟨tau_mem_zjVh Mc t τ l, htauCentV⟩

theorem V_unique {W : Subgroup H} (hW : W ≤ zjVh Mc t τ l)
    (hWn : ∀ g ∈ zjVh Mc t τ l, ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hWd : W ≤ ⁅zjVh Mc t τ l, zjVh Mc t τ l⁆) (hW4 : Nat.card W = 4)
    (hWe : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1) : W = V := by
  have hcomm_le_Mc : ⁅zjVh Mc t τ l, zjVh Mc t τ l⁆ ≤ Mc := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    simpa [commutatorElement_def] using comm_Vh_mem_Mc h hMh hMc ha hb
  have hWMc : W ≤ Mc := hWd.trans hcomm_le_Mc
  have hVQ : V ≤ Q := by
    intro x hx
    exact h.Y_le_Q (by rw [h.Y_eq]; exact Subgroup.mem_sup_left hx)
  have hVleW_of_not : ∀ w ∈ W, w ∉ V → V ≤ W := by
    intro w hwW hwV
    have hwMc : w ∈ Mc := hWMc hwW
    have hww1 : w * w = 1 := (hWe w hwW w hwW).2
    intro v hv
    by_cases hwQ : w ∈ Q
    · have hwY : w ∈ Y := h.Y_mem w hwQ hww1
      obtain ⟨m, hm, hmeq⟩ := exists_conj_Mc h hMh hMc hwY hwV hv
      have hmVh : m ∈ zjVh Mc t τ l := Mc_le_zjVh Mc t τ l hm
      have hmemW : m * w * m⁻¹ * w⁻¹ ∈ W :=
        W.mul_mem (hWn m hmVh w hwW) (W.inv_mem hwW)
      have hvEq : m * w * m⁻¹ * w⁻¹ = v := by
        rw [hmeq]
        have hvQ : v ∈ Q := hVQ hv
        rw [h.Q_comm w hwQ v hvQ]
        group
      rw [← hvEq]
      exact hmemW
    · obtain ⟨u, huY, hueq⟩ := exists_conj_Y h hMh hMc hwMc hwQ hv
      have huVh : u ∈ zjVh Mc t τ l :=
        Mc_le_zjVh Mc t τ l (Q_le_Mc h hMh hMc (h.Y_le_Q huY))
      have hmemW : u * w * u⁻¹ * w⁻¹ ∈ W :=
        W.mul_mem (hWn u huVh w hwW) (W.inv_mem hwW)
      have hvEq : u * w * u⁻¹ * w⁻¹ = v := by
        rw [hueq]
        have hcent : w * v * w⁻¹ = v := Mh_cent_V h hMh (Mc_le_Mh h hMh hMc hwMc) hv
        rw [hcent]
      rw [← hvEq]
      exact hmemW
  by_cases hWV : W ≤ V
  · exact Subgroup.eq_of_le_of_card_ge hWV (by rw [h.card_V, hW4])
  · have hlt : ∃ w, w ∈ W ∧ w ∉ V := by
      by_contra hcon
      exact hWV (fun w hw => by
        by_contra hwV
        exact hcon ⟨w, hw, hwV⟩)
    obtain ⟨w, hwW, hwV⟩ := hlt
    have hVW : V ≤ W := hVleW_of_not w hwW hwV
    have hVeqW : V = W := Subgroup.eq_of_le_of_card_ge hVW (by rw [hW4, h.card_V])
    exact absurd (hVeqW.symm ▸ hwW) hwV

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
