module

public import CFSG.CGT.Foote82.T66.BranchASmallDim
import CFSG.CGT.Foote82.T66.OddTranspTools

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

private theorem closure_comm {Γ : Type*} [Group Γ] {S : Set Γ}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact hS b hb a ha
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set Γ) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    have := h1 hb
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this a ha).symm
  intro x hx y hy
  have := h2 hy
  rw [Subgroup.mem_centralizer_iff] at this
  exact this x hx

theorem mem_centralizer_of_forall_commute {e : GLV V} (hq : Open.IsQuasisimple ↥L)
    (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (he : e * e = 1)
    (heN : e ∈ Subgroup.normalizer (L : Set (GLV V)))
    (hcomm : ∀ l ∈ L, e * (l * e * l⁻¹) = (l * e * l⁻¹) * e) :
    e ∈ Subgroup.centralizer (L : Set (GLV V)) := by
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  set S : Set (GLV V) := {x | ∃ l ∈ L, x = l * e * l⁻¹} with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro _ ⟨l, hl, rfl⟩ _ ⟨m, hm, rfl⟩
    have h := hcomm (l⁻¹ * m) (L.mul_mem (L.inv_mem hl) hm)
    calc l * e * l⁻¹ * (m * e * m⁻¹) = l * (e * ((l⁻¹ * m) * e * (l⁻¹ * m)⁻¹)) * l⁻¹ := by group
      _ = l * (((l⁻¹ * m) * e * (l⁻¹ * m)⁻¹) * e) * l⁻¹ := by rw [h]
      _ = m * e * m⁻¹ * (l * e * l⁻¹) := by group
  set E := Subgroup.closure S with hE
  have hEcomm := closure_comm hS
  have heE : e ∈ E := Subgroup.subset_closure ⟨1, L.one_mem, by simp⟩
  have hnorm : ∀ x ∈ L, ∀ n ∈ L ⊓ E, x * n * x⁻¹ ∈ L ⊓ E := by
    intro x hx n hn
    refine ⟨L.mul_mem (L.mul_mem hx hn.1) (L.inv_mem hx), ?_⟩
    have hEx : E ≤ E.comap (MulAut.conj x).toMonoidHom := by
      rw [hE, Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      show x * (l * e * l⁻¹) * x⁻¹ ∈ Subgroup.closure S
      exact Subgroup.subset_closure ⟨x * l, L.mul_mem hx hl, by group⟩
    exact hEx hn.2
  have hcent : ∀ n ∈ L ⊓ E, ∀ a ∈ L, n * a = a * n := by
    rcases CFSG.LargeExtraspecial.S5.commute_or_eq_of_normalized hq inf_le_left hnorm with h | h
    · exact h
    · exfalso
      have hLE : L ≤ E := fun x hx => by
        have : x ∈ L ⊓ E := h.symm ▸ hx
        exact this.2
      have hb : ⁅L, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact hEcomm _ (hLE hb) _ (hLE ha)
      exact hL1 (hperf ▸ hb)
  have hφL : ∀ l ∈ L, l * e * l⁻¹ * e⁻¹ ∈ L := fun l hl => by
    have h1 : e * l⁻¹ * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 heN l⁻¹).1 (L.inv_mem hl)
    have h2 : l * e * l⁻¹ * e⁻¹ = l * (e * l⁻¹ * e⁻¹) := by group
    rw [h2]
    exact L.mul_mem hl h1
  have hφE : ∀ l ∈ L, l * e * l⁻¹ * e⁻¹ ∈ E := fun l hl =>
    E.mul_mem (Subgroup.subset_closure ⟨l, hl, rfl⟩) (E.inv_mem heE)
  have hφc : ∀ l ∈ L, ∀ a ∈ L, (l * e * l⁻¹ * e⁻¹) * a = a * (l * e * l⁻¹ * e⁻¹) :=
    fun l hl => hcent _ ⟨hφL l hl, hφE l hl⟩
  have hφmul : ∀ a ∈ L, ∀ b ∈ L, (a * b) * e * (a * b)⁻¹ * e⁻¹ =
      (a * e * a⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) := by
    intro a ha b hb
    have h1 := hφc b hb a ha
    calc (a * b) * e * (a * b)⁻¹ * e⁻¹
        = a * (b * e * b⁻¹ * e⁻¹) * (e * a⁻¹ * e⁻¹) := by group
      _ = (b * e * b⁻¹ * e⁻¹) * a * (e * a⁻¹ * e⁻¹) := by rw [← h1]
      _ = (b * e * b⁻¹ * e⁻¹) * (a * e * a⁻¹ * e⁻¹) := by group
      _ = (a * e * a⁻¹ * e⁻¹) * (b * e * b⁻¹ * e⁻¹) := (hφc b hb _ (hφL a ha))
  have hinv : ∀ x ∈ L, x⁻¹ * e * x⁻¹⁻¹ * e⁻¹ = (x * e * x⁻¹ * e⁻¹)⁻¹ := by
    intro x hx
    have h1 := hφmul x hx x⁻¹ (L.inv_mem hx)
    have h1' : (x * e * x⁻¹ * e⁻¹) * (x⁻¹ * e * x⁻¹⁻¹ * e⁻¹) = 1 := by
      rw [← h1]
      group
    exact eq_inv_of_mul_eq_one_right h1'
  have hle : ⁅L, L⁆ ≤ Subgroup.centralizer ({e} : Set (GLV V)) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    set A := a * e * a⁻¹ * e⁻¹ with hA
    set B := b * e * b⁻¹ * e⁻¹ with hB
    have hab : A * B = B * A := hφc a ha _ (hφL b hb)
    have h1 := hφmul (a * b) (L.mul_mem ha hb) (a⁻¹ * b⁻¹) (L.mul_mem (L.inv_mem ha) (L.inv_mem hb))
    rw [hφmul a ha b hb, hφmul a⁻¹ (L.inv_mem ha) b⁻¹ (L.inv_mem hb), hinv a ha, hinv b hb]
      at h1
    have h2 : (a * b * (a⁻¹ * b⁻¹)) * e * (a * b * (a⁻¹ * b⁻¹))⁻¹ * e⁻¹ = 1 := by
      rw [h1]
      calc A * B * (A⁻¹ * B⁻¹) = B * A * (A⁻¹ * B⁻¹) := by rw [hab]
        _ = 1 := by group
    have h3 : (a * b * (a⁻¹ * b⁻¹)) * e = e * (a * b * (a⁻¹ * b⁻¹)) := by
      calc (a * b * (a⁻¹ * b⁻¹)) * e
          = ((a * b * (a⁻¹ * b⁻¹)) * e * (a * b * (a⁻¹ * b⁻¹))⁻¹ * e⁻¹) * e *
              (a * b * (a⁻¹ * b⁻¹)) := by group
        _ = e * (a * b * (a⁻¹ * b⁻¹)) := by rw [h2, one_mul]
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ * e = (a * b * (a⁻¹ * b⁻¹)) * e := by group
      _ = e * (a * b * (a⁻¹ * b⁻¹)) := h3
      _ = e * (a * b * a⁻¹ * b⁻¹) := by group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := hle (hperf.symm ▸ hl)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem conj_z_mul_self (g : GLV V) : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hc.z_mul_z, mul_one, mul_inv_cancel]

theorem oddTransp_conj {h : GLV V} (hh : h ∈ G) (l : GLV V) (hl : l ∈ L) :
    orderOf ((h * z * h⁻¹) * (l * (h * z * h⁻¹) * l⁻¹)) ≤ 2 ∨
      Odd (orderOf ((h * z * h⁻¹) * (l * (h * z * h⁻¹) * l⁻¹))) := by
  have h1 := hc.conf.oddTransp h hh (l * h) (G.mul_mem (hc.L_le hl) hh)
  have h2 : (l * h) * z * (l * h)⁻¹ = l * (h * z * h⁻¹) * l⁻¹ := by group
  rwa [h2] at h1

theorem finrank_commSpace_conj_z (h : GLV V) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (h * z * h⁻¹)) ⊤) =
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) := by
  rw [commSpace_zpowers_conj, finrank_conjSub]

theorem le_normalizer_of_transv {h : GLV V} (hh : h ∈ G) (hne : h * z * h⁻¹ ≠ z)
    (hcomm : (h * z * h⁻¹) * z = z * (h * z * h⁻¹))
    (hrank : Module.finrank (ZMod 2) ↥(tvComm L (h * z * h⁻¹)) =
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1)
    (hmax : IsCoatom ((L ⊓ Subgroup.centralizer ({h * z * h⁻¹} : Set (GLV V))).subgroupOf L))
    (hdim : 2 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤)) :
    L ≤ Subgroup.normalizer (conjSg h L : Set (GLV V)) := by
  set e := h * z * h⁻¹ with he_def
  obtain ⟨heN, heC⟩ := hc.mem_normalizer_of_Dz hh hne hcomm
  have he2 : e * e = 1 := hc.conj_z_mul_self h
  have heo : orderOf e = 2 := hc.orderOf_conj_z h
  have heG : e ∈ G := hc.conj_z_mem hh
  have hCe : L ⊓ Subgroup.centralizer ({e} : Set (GLV V)) ≤
      Subgroup.normalizer (conjSg h L : Set (GLV V)) := fun x hx =>
    hc.centralizer_conj_z_le hh ⟨hc.L_le hx.1, hx.2⟩
  obtain ⟨l₀, hl₀, hl₀c⟩ : ∃ l ∈ L, e * (l * e * l⁻¹) ≠ (l * e * l⁻¹) * e := by
    by_contra hall
    push Not at hall
    exact heC (mem_centralizer_of_forall_commute hc.quasisimple hc.perfect hc.L_ne_bot he2 heN
      hall)
  set f := l₀ * e * l₀⁻¹ with hf_def
  have hf2 : f * f = 1 := by
    calc f * f = l₀ * (e * e) * l₀⁻¹ := by rw [hf_def]; group
      _ = 1 := by rw [he2, mul_one, mul_inv_cancel]
  have hfo : orderOf f = 2 := by rw [hf_def, orderOf_conj, heo]
  have hfG : f = (l₀ * h) * z * (l₀ * h)⁻¹ := by rw [hf_def, he_def]; group
  have hl₀hG : l₀ * h ∈ G := G.mul_mem (hc.L_le hl₀) hh
  have hfN : f ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hl₀) heN)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hl₀))
  set c := e * f with hc_def
  have hcL : c ∈ L := by
    have h1 : e * l₀ * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 heN l₀).1 hl₀
    have h2 : c = (e * l₀ * e⁻¹) * l₀⁻¹ := by
      rw [hc_def, hf_def, inv_eq_of_mul_eq_one_right he2]
      group
    rw [h2]
    exact L.mul_mem h1 (L.inv_mem hl₀)
  have hc1 : c ≠ 1 := by
    intro h1
    apply hl₀c
    have : f = e := by
      have h2 : e * c = e := by rw [h1, mul_one]
      rw [hc_def, ← mul_assoc, he2, one_mul] at h2
      exact h2
    rw [hc_def, this]
  have hcodd : Odd (orderOf c) := by
    rcases hc.oddTransp_conj hh l₀ hl₀ with h1 | h1
    · exfalso
      apply hl₀c
      have hpos : 0 < orderOf c := (isOfFinOrder_of_finite c).orderOf_pos
      have hdvd : orderOf c ∣ 2 := by
        interval_cases hk : orderOf c
        · exact one_dvd 2
        · exact dvd_refl 2
      have hc2 : c * c = 1 := by
        have := orderOf_dvd_iff_pow_eq_one.1 hdvd
        rwa [sq] at this
      have hcinv : c = c⁻¹ := eq_inv_of_mul_eq_one_left hc2
      calc e * f = c := rfl
        _ = c⁻¹ := hcinv
        _ = f⁻¹ * e⁻¹ := by rw [hc_def, mul_inv_rev]
        _ = f * e := by rw [inv_eq_of_mul_eq_one_right hf2, inv_eq_of_mul_eq_one_right he2]
    · exact h1
  have hfC : f ∈ Subgroup.centralizer (conjSg h L : Set (GLV V)) := by
    by_contra hfC
    have hdis : commSpace (Subgroup.zpowers e) ⊤ ⊓ commSpace (Subgroup.zpowers f) ⊤ = ⊥ := by
      by_contra hne'
      rw [hfG] at hne'
      have heq := hc.eq_of_commSpace_inf hh hl₀hG hne'
      apply hfC
      rw [heq, hfG]
      exact hc.conj_z_mem_centralizer _
    have hs3 := (s3_trick heo hfo hcodd hc1 hdis).2
    have h1 := finrank_commSpace_add_le hcL hcodd
    have h2 : Module.finrank (ZMod 2) ↥(tvComm L c) ≤
        Module.finrank (ZMod 2) ↥(tvComm L e ⊔ tvComm L f) :=
      Submodule.finrank_mono (tvComm_mul_le he2 hf2 heN hfN)
    have h3 := finrank_tvComm_sup_le L e f
    have h4 : Module.finrank (ZMod 2) ↥(tvComm L f) = Module.finrank (ZMod 2) ↥(tvComm L e) :=
      finrank_tvComm_conj hl₀ e
    have h5 : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers e) ⊤) =
        Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) :=
      hc.finrank_commSpace_conj_z h
    have hs3' : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) =
        2 * Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers e) ⊤) := hs3
    omega
  have hl₀N : l₀ ∈ Subgroup.normalizer (conjSg h L : Set (GLV V)) := by
    have hfG' : f ∈ G := hfG ▸ hc.conj_z_mem hl₀hG
    have hcomp1 := hc.component_of_inv_conj hh hfG' hfo hfC
    have hcomp2 := hc.component_conj hl₀hG
    rw [← hfG] at hcomp2
    have heq := hc.eq_of_isComponentOf hh hl₀hG hcomp1 hcomp2
    rw [mem_normalizer_iff_conjSg_eq, ← conjSg_mul, heq]
  have hl₀notC : l₀ ∉ Subgroup.centralizer ({e} : Set (GLV V)) := by
    intro h1
    apply hl₀c
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have : f = e := by rw [hf_def, h1, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc_def, this]
  set H := (Subgroup.normalizer (conjSg h L : Set (GLV V)) ⊓ L).subgroupOf L with hH
  have hlt : (L ⊓ Subgroup.centralizer ({e} : Set (GLV V))).subgroupOf L < H := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hCe hx, hx.1⟩
    · intro heq
      have hmem : (⟨l₀, hl₀⟩ : ↥L) ∈ H := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hl₀N, hl₀⟩
      rw [← heq, Subgroup.mem_subgroupOf] at hmem
      exact hl₀notC hmem.2
  have htop := hmax.2 H hlt
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥L) ∈ H := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf] at hmem
  exact hmem.1

theorem lt_finrank_tvComm {k : GLV V} (hk : k ∈ G) (hne : k * z * k⁻¹ ≠ z)
    (hcomm : (k * z * k⁻¹) * z = z * (k * z * k⁻¹)) :
    Module.finrank (ZMod 2) ↥(tildeVBot L) < Module.finrank (ZMod 2) ↥(tvComm L (k * z * k⁻¹)) := by
  obtain ⟨hN, hC⟩ := hc.mem_normalizer_of_Dz hk hne hcomm
  by_contra hle
  push Not at hle
  have heq := Submodule.eq_of_le_of_finrank_le (le_sup_right : tildeVBot L ≤ tvComm L _) hle
  exact hC (mem_centralizer_of_tvComm_le hc.faithful (hc.conj_z_mul_self k) hN heq.symm.le)

theorem finrank_commSpace_z_le_one
    (hmax : ∀ d ∈ Subgroup.normalizer (L : Set (GLV V)), orderOf d = 2 →
      Module.finrank (ZMod 2) ↥(tvComm L d) = Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 →
      IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L))
    (hbig : ∀ g ∈ G, g * z * g⁻¹ ≠ z → (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      Module.finrank (ZMod 2) ↥(tvComm L (g * z * g⁻¹)) ≤
        Module.finrank (ZMod 2) ↥(tildeVBot L) + 1) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hdim : 2 ≤ Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) := hlt
  have hrank : ∀ k ∈ G, k * z * k⁻¹ ≠ z → (k * z * k⁻¹) * z = z * (k * z * k⁻¹) →
      Module.finrank (ZMod 2) ↥(tvComm L (k * z * k⁻¹)) =
        Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 := by
    intro k hk hne hcomm
    have h1 := hbig k hk hne hcomm
    have h2 := hc.lt_finrank_tvComm hk hne hcomm
    omega
  obtain ⟨g, hg, hne, hcomm⟩ := hc.exists_Dz
  have hne' : g⁻¹ * z * g⁻¹⁻¹ ≠ z := by
    intro h1
    apply hne
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ := by rw [h1]
      _ = z := by group
  have hcomm' : (g⁻¹ * z * g⁻¹⁻¹) * z = z * (g⁻¹ * z * g⁻¹⁻¹) := by
    calc (g⁻¹ * z * g⁻¹⁻¹) * z = g⁻¹ * (z * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * z) * g := by rw [hcomm]
      _ = z * (g⁻¹ * z * g⁻¹⁻¹) := by group
  have hg' : g⁻¹ ∈ G := G.inv_mem hg
  have hN1 := hc.le_normalizer_of_transv hg hne hcomm (hrank g hg hne hcomm)
    (hmax _ (hc.mem_normalizer_of_Dz hg hne hcomm).1 (hc.orderOf_conj_z g)
      (hrank g hg hne hcomm)) hdim
  have hN2 := hc.le_normalizer_of_transv hg' hne' hcomm' (hrank _ hg' hne' hcomm')
    (hmax _ (hc.mem_normalizer_of_Dz hg' hne' hcomm').1 (hc.orderOf_conj_z g⁻¹)
      (hrank _ hg' hne' hcomm')) hdim
  have hN2' : conjSg g L ≤ Subgroup.normalizer (L : Set (GLV V)) := by
    have := conjSg_mono (g := g) hN2
    rwa [conjSg_normalizer, conjSg_conjSg_inv] at this
  have heq := hc.eq_of_normalizes G.one_mem hg (by rwa [conjSg_one]) (by rwa [conjSg_one])
  rw [conjSg_one] at heq
  apply (hc.mem_normalizer_of_Dz hg hne hcomm).2
  rw [heq]
  exact hc.conj_z_mem_centralizer g

end Hyp

end CFSG.CGT.Foote82.BAS
