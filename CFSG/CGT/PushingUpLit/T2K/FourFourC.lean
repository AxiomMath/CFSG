module

public import CFSG.CGT.PushingUpLit.T2K.FourFourB

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly CFSG.Quasithin
  CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem map_conj_eq_of_mem_normalizer {G : Type} [Group G] {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : X.map (MulAut.conj g).toMonoidHom = X := by
  ext x
  rw [mem_map_conj_iff]
  have := Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e] at this
  exact this

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {s : G}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple) (hs : orderOf s = 4)
  (hX : Subgroup.centralizer (L : Set G) = Subgroup.zpowers s)
include h hE1 hs hX

omit [Finite G] h hE1 in
theorem z4_Y_sq {g w : G}
    (hw : w ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hw2 : w ^ 2 = 1) : w = 1 ∨ w = (g * s * g⁻¹) ^ 2 := by
  rw [mem_map_conj_iff] at hw
  have hx2 : (g⁻¹ * w * g) ^ 2 = 1 := by
    have e : g⁻¹ * w * g = g⁻¹ * w * (g⁻¹)⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hw2]
    group
  rw [hX] at hw
  have e : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
  rcases zpowers_sq_eq_one hs hw hx2 with h1 | h1
  · left
    rw [e, h1]
    group
  · right
    rw [e, h1, conj_pow]

theorem z4_Y_norm {g c : G} (hc : c * (g * s * g⁻¹) ^ 2 * c⁻¹ = (g * s * g⁻¹) ^ 2) {w : G}
    (hw : w ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) :
    c * w * c⁻¹ ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom := by
  have hc' : (g⁻¹ * c * g) * s ^ 2 * (g⁻¹ * c * g)⁻¹ = s ^ 2 := by
    rw [conj_pow] at hc
    calc (g⁻¹ * c * g) * s ^ 2 * (g⁻¹ * c * g)⁻¹
        = g⁻¹ * (c * (g * s ^ 2 * g⁻¹) * c⁻¹) * g := by group
      _ = g⁻¹ * (g * s ^ 2 * g⁻¹) * g := by rw [hc]
      _ = s ^ 2 := by group
  have hcM : g⁻¹ * c * g ∈ M := h.z4_cent_le hE1 hs hX hc'
  rw [mem_map_conj_iff] at hw ⊢
  have h1 := (Subgroup.mem_normalizer_iff.1 (h.le_normalizer_centralizer hE1 hcM)
    (g⁻¹ * w * g)).1 hw
  have e : (g⁻¹ * c * g) * (g⁻¹ * w * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * w * c⁻¹) * g := by group
  rw [e] at h1
  exact h1

theorem z4_y_centralizes (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {g : G}
    (hgT : (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤ T) :
    ∀ v ∈ blockU L, (g * s * g⁻¹) * v * (g * s * g⁻¹)⁻¹ = v := by
  classical
  have hMN := h.normal hE1
  have hBlock := h.natBlock
  set y : G := g * s * g⁻¹ with hydef
  set a : G := y ^ 2 with hadef
  set Y : Subgroup G := (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom
    with hYdef
  have hsX : s ∈ Subgroup.centralizer (L : Set G) := by
    rw [hX]
    exact Subgroup.mem_zpowers s
  have hyY : y ∈ Y := ⟨s, hsX, by simp [hydef, MulAut.conj_apply]⟩
  have hyT : y ∈ T := hgT hyY
  have hyM : y ∈ M := hT.le hyT
  have hyN : y ∈ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le hMN hyM
  have hyinvN : y⁻¹ ∈ Subgroup.normalizer (blockU L : Set G) :=
    (Subgroup.normalizer (blockU L : Set G)).inv_mem hyN
  have hyV : ∀ u ∈ blockU L, y * u * y⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.1 hyN u).1 hu
  have hy4 : y ^ 4 = 1 := by
    rw [hydef, conj_pow, pow_four_eq_one_of_orderOf_four hs]
    group
  have hYV : ∀ w ∈ Y, w ∈ blockU L → w = 1 ∨ (w = a ∧ a ∈ blockU L) := by
    intro w hwY hwV
    rcases z4_Y_sq hs hX hwY (hBlock.sq_eq_one_of_mem_blockU hwV) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by rw [show a = w from h1.symm]; exact hwV⟩
  have hYn : ∀ c, c * a * c⁻¹ = a → ∀ w ∈ Y, c * w * c⁻¹ ∈ Y := fun c hc w hw =>
    h.z4_Y_norm hE1 hs hX hc hw
  by_cases haV : a ∈ blockU L
  ·
    by_contra hnot
    push Not at hnot
    obtain ⟨v₀, hv₀, hv₀ne⟩ := hnot
    have hVcomm := hBlock.blockU_comm
    have hδ : ∀ v ∈ blockU L, y * v * y⁻¹ * v⁻¹ = 1 ∨ y * v * y⁻¹ * v⁻¹ = a := by
      intro v hv
      have hva : v * a * v⁻¹ = a := by
        have : v * a = a * v := hVcomm v hv a haV
        calc v * a * v⁻¹ = (a * v) * v⁻¹ := by rw [this]
          _ = a := by group
      have h1 : v * y⁻¹ * v⁻¹ ∈ Y := hYn v hva y⁻¹ (Y.inv_mem hyY)
      have h2 : y * (v * y⁻¹ * v⁻¹) ∈ Y := Y.mul_mem hyY h1
      have e : y * (v * y⁻¹ * v⁻¹) = y * v * y⁻¹ * v⁻¹ := by group
      rw [e] at h2
      have h3 : y * v * y⁻¹ * v⁻¹ ∈ blockU L :=
        (blockU L).mul_mem (hyV v hv) ((blockU L).inv_mem hv)
      rcases hYV _ h2 h3 with h4 | ⟨h4, -⟩
      · exact Or.inl h4
      · exact Or.inr h4
    have hδ0 : y * v₀ * y⁻¹ * v₀⁻¹ = a := by
      rcases hδ v₀ hv₀ with h1 | h1
      · exfalso
        apply hv₀ne
        calc y * v₀ * y⁻¹ = (y * v₀ * y⁻¹ * v₀⁻¹) * v₀ := by group
          _ = v₀ := by rw [h1]; group
      · exact h1
    have hyv₀ : y * v₀ * y⁻¹ = a * v₀ := by
      calc y * v₀ * y⁻¹ = (y * v₀ * y⁻¹ * v₀⁻¹) * v₀ := by group
        _ = a * v₀ := by rw [hδ0]
    have hv₀2 : v₀ * v₀ = 1 := by
      rw [← pow_two]
      exact hBlock.sq_eq_one_of_mem_blockU hv₀
    have ha2' : a * a = 1 := by
      rw [← pow_two]
      exact hBlock.sq_eq_one_of_mem_blockU haV
    have ht2 : (y * v₀) ^ 2 = 1 := by
      have e : (y * v₀) ^ 2 = (y * v₀ * y⁻¹) * (y * y) * v₀ := by
        rw [pow_two]
        group
      have hyy : y * y = a := by rw [hadef, pow_two]
      rw [e, hyv₀, hyy]
      have hav : a * v₀ = v₀ * a := hVcomm a haV v₀ hv₀
      calc a * v₀ * a * v₀ = a * (v₀ * a) * v₀ := by group
        _ = a * (a * v₀) * v₀ := by rw [hav]
        _ = (a * a) * (v₀ * v₀) := by group
        _ = 1 := by rw [ha2', hv₀2, mul_one]
    have htM : y * v₀ ∈ M := M.mul_mem hyM (h.le (blockU_le L hv₀))
    have hKidx : (blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)).relIndex (blockU L) ≤ 2 := by
      let _ : CommGroup ↥(blockU L) := commGroupOfElemAbelian hBlock.isElemAbelian_blockU
      let φ : MulAut ↥(blockU L) := conjAct (blockU L) ⟨y, hyN⟩
      have hφ : ∀ w : ↥(blockU L), ((φ w : ↥(blockU L)) : G) = y * w * y⁻¹ := fun w =>
        conjAct_apply' (blockU L) ⟨y, hyN⟩ w
      let δ : ↥(blockU L) →* ↥(blockU L) := MonoidHom.mk' (fun w => φ w * w⁻¹) (fun b c => by
        simp only [map_mul, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm])
      have hδG : ∀ w : ↥(blockU L), ((δ w : ↥(blockU L)) : G) = y * w * y⁻¹ * (w : G)⁻¹ := by
        intro w
        show (((φ w * w⁻¹ : ↥(blockU L))) : G) = _
        rw [Subgroup.coe_mul, hφ, Subgroup.coe_inv]
      have hker : δ.ker = (blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)).subgroupOf
          (blockU L) := by
        ext w
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        have hwv : (w : G) * v₀ = v₀ * (w : G) := hVcomm w w.2 v₀ hv₀
        constructor
        · intro hw
          have h1 : y * (w : G) * y⁻¹ * (w : G)⁻¹ = 1 := by
            have := congrArg (fun x : ↥(blockU L) => (x : G)) hw
            simpa [hδG] using this
          have h2 : y * (w : G) = (w : G) * y := by
            calc y * (w : G) = (y * (w : G) * y⁻¹ * (w : G)⁻¹) * ((w : G) * y) := by group
              _ = (w : G) * y := by rw [h1, one_mul]
          refine ⟨w.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
          calc (w : G) * (y * v₀) = ((w : G) * y) * v₀ := by group
            _ = (y * (w : G)) * v₀ := by rw [h2]
            _ = y * ((w : G) * v₀) := by group
            _ = y * (v₀ * (w : G)) := by rw [hwv]
            _ = (y * v₀) * (w : G) := by group
        · intro hw
          have h1 := Subgroup.mem_centralizer_singleton_iff.1 hw.2
          have h2 : (w : G) * y = y * (w : G) := by
            have h3 : ((w : G) * y) * v₀ = (y * (w : G)) * v₀ := by
              calc ((w : G) * y) * v₀ = (w : G) * (y * v₀) := by group
                _ = (y * v₀) * (w : G) := h1
                _ = y * (v₀ * (w : G)) := by group
                _ = y * ((w : G) * v₀) := by rw [hwv]
                _ = (y * (w : G)) * v₀ := by group
            exact mul_right_cancel h3
          apply Subtype.ext
          rw [hδG, Subgroup.coe_one]
          calc y * (w : G) * y⁻¹ * (w : G)⁻¹ = ((w : G) * y) * y⁻¹ * (w : G)⁻¹ := by rw [h2]
            _ = 1 := by group
      have hrange : Nat.card δ.range ≤ 2 := by
        have hle : δ.range ≤ Subgroup.zpowers (⟨a, haV⟩ : ↥(blockU L)) := by
          rintro _ ⟨w, rfl⟩
          rcases hδ (w : G) w.2 with h1 | h1
          · have : δ w = 1 := Subtype.ext (by rw [hδG, Subgroup.coe_one]; exact h1)
            rw [this]
            exact one_mem _
          · have : δ w = ⟨a, haV⟩ := Subtype.ext (by rw [hδG]; exact h1)
            rw [this]
            exact Subgroup.mem_zpowers _
        refine (Subgroup.card_le_of_le hle).trans ?_
        rw [Nat.card_zpowers]
        refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
        exact Subtype.ext (by simpa using hBlock.sq_eq_one_of_mem_blockU haV)
      calc (blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)).relIndex (blockU L)
          = ((blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)).subgroupOf (blockU L)).index :=
            rfl
        _ = δ.ker.index := by rw [hker]
        _ = Nat.card δ.range := Subgroup.index_ker δ
        _ ≤ 2 := hrange
    have hidx : Nat.card ↥(blockU L) ≤
        2 * Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)) := by
      have h1 := Subgroup.relIndex_mul_card
        (blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)) (blockU L)
      rw [inf_of_le_left (inf_le_left : blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G) ≤
        blockU L)] at h1
      calc Nat.card ↥(blockU L) = _ := h1.symm
        _ ≤ 2 * Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({y * v₀} : Set G)) :=
          Nat.mul_le_mul_right _ hKidx
    have htC := hBlock.centralizes_of_index_le_two h.le hMN htM ht2 hidx
    have hv₀t := Subgroup.mem_centralizer_iff.1 htC v₀ hv₀
    have e1 : v₀ * y * v₀ = y := by
      calc v₀ * y * v₀ = v₀ * (y * v₀) := by group
        _ = (y * v₀) * v₀ := hv₀t
        _ = y * (v₀ * v₀) := by group
        _ = y := by rw [hv₀2, mul_one]
    have e2 : v₀ * y = y * v₀ := by
      calc v₀ * y = (v₀ * y * v₀) * v₀⁻¹ := by group
        _ = y * v₀⁻¹ := by rw [e1]
        _ = y * v₀ := by rw [inv_eq_of_mul_eq_one_right hv₀2]
    apply hv₀ne
    calc y * v₀ * y⁻¹ = (v₀ * y) * y⁻¹ := by rw [e2]
      _ = v₀ := by group
  ·
    refine centralizes_of_fixed_sq hBlock.isElemAbelian_blockU hyN hy4 ?_
    intro u hu hua
    have hcomm0 : a * u = u * a := by
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [show a * u * a⁻¹ = u from hua]
    have hcomm : u * a * u⁻¹ = a := by
      calc u * a * u⁻¹ = (a * u) * u⁻¹ := by rw [hcomm0]
        _ = a := by group
    have h1 : u * y * u⁻¹ ∈ Y := hYn u hcomm y hyY
    have h2 : y⁻¹ * (u * y * u⁻¹) ∈ Y := Y.mul_mem (Y.inv_mem hyY) h1
    have h3 : y⁻¹ * (u * y * u⁻¹) ∈ blockU L := by
      have e : y⁻¹ * (u * y * u⁻¹) = (y⁻¹ * u * y) * u⁻¹ := by group
      rw [e]
      refine (blockU L).mul_mem ?_ ((blockU L).inv_mem hu)
      have := (Subgroup.mem_normalizer_iff.1 hyinvN u).1 hu
      simpa using this
    rcases hYV _ h2 h3 with h4 | ⟨-, h4⟩
    · have e1 : u * y * u⁻¹ = y := by
        calc u * y * u⁻¹ = y * (y⁻¹ * (u * y * u⁻¹)) := by group
          _ = y := by rw [h4]; group
      have e2 : u * y = y * u := by
        calc u * y = (u * y * u⁻¹) * u := by group
          _ = y * u := by rw [e1]
      calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [e2]
        _ = u := by group
    · exact absurd h4 haV

theorem z4_conj_eq (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) {g : G}
    (hgT : (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤ T) :
    (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (L : Set G) := by
  classical
  by_contra hgX
  have hMN := h.normal hE1
  have hBlock := h.natBlock
  have hgM : g ∉ M := fun hg =>
    hgX (map_conj_eq_of_mem_normalizer (h.le_normalizer_centralizer hE1 hg))
  have hyC := h.z4_y_centralizes hE1 hs hX hT hgT
  set y : G := g * s * g⁻¹ with hydef
  set a : G := y ^ 2 with hadef
  set Y : Subgroup G := (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom
    with hYdef
  have hsX : s ∈ Subgroup.centralizer (L : Set G) := by
    rw [hX]
    exact Subgroup.mem_zpowers s
  have hyY : y ∈ Y := ⟨s, hsX, by simp [hydef, MulAut.conj_apply]⟩
  have hyM : y ∈ M := hT.le (hgT hyY)
  have hyCV : y ∈ Subgroup.centralizer (blockU L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    calc v * y = (y * v * y⁻¹) * y := by rw [hyC v hv]
      _ = y * v := by group
  have hyMC : y ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨hyM, hyCV⟩
  have hadef' : a = g * s ^ 2 * g⁻¹ := by rw [hadef, hydef, conj_pow]
  have ha1 : a ≠ 1 := by
    intro h1
    apply sq_ne_one_of_orderOf_four hs
    have e : s ^ 2 = g⁻¹ * a * g := by rw [hadef']; group
    rw [e, h1]
    group
  have haY : a ∈ Y := Y.pow_mem hyY 2
  have hYV : ∀ w ∈ Y, w ∈ blockU L → w = 1 ∨ w = a := by
    intro w hwY hwV
    exact z4_Y_sq hs hX hwY (hBlock.sq_eq_one_of_mem_blockU hwV)
  have key : ∀ l ∈ L, l * a * l⁻¹ = a ∧ (⁅y, l⁆ = 1 ∨ ⁅y, l⁆ = a) := by
    intro l hl
    have hκV : ⁅y, l⁆ ∈ blockU L := hBlock.comm_centralizer_mem_blockU hMN hyMC l hl
    have hlyl : l * y * l⁻¹ = (⁅y, l⁆)⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    have hκinv : (⁅y, l⁆)⁻¹ ∈ blockU L := (blockU L).inv_mem hκV
    have hκy : y * (⁅y, l⁆)⁻¹ = (⁅y, l⁆)⁻¹ * y :=
      (Subgroup.mem_centralizer_iff.1 hyCV _ hκinv).symm
    have hκ2 : (⁅y, l⁆)⁻¹ * (⁅y, l⁆)⁻¹ = 1 := by
      rw [← pow_two]
      exact hBlock.sq_eq_one_of_mem_blockU hκinv
    have hsq : (l * y * l⁻¹) ^ 2 = a := by
      rw [hlyl, pow_two]
      calc (⁅y, l⁆)⁻¹ * y * ((⁅y, l⁆)⁻¹ * y) = (⁅y, l⁆)⁻¹ * (y * (⁅y, l⁆)⁻¹) * y := by group
        _ = (⁅y, l⁆)⁻¹ * ((⁅y, l⁆)⁻¹ * y) * y := by rw [hκy]
        _ = ((⁅y, l⁆)⁻¹ * (⁅y, l⁆)⁻¹) * (y * y) := by group
        _ = a := by rw [hκ2, one_mul, hadef, pow_two]
    have hla : l * a * l⁻¹ = a := by
      have h1 : l * y ^ 2 * l⁻¹ = (l * y * l⁻¹) ^ 2 := conj_pow.symm
      rw [hsq] at h1
      exact h1
    refine ⟨hla, ?_⟩
    have hlY : l * y * l⁻¹ ∈ Y := by
      have hmem : l * y * l⁻¹ ∈ (Subgroup.centralizer (L : Set G)).map
          (MulAut.conj (l * g)).toMonoidHom :=
        ⟨s, hsX, by simp [hydef, MulAut.conj_apply, mul_assoc]⟩
      have hamem : a ∈ (Subgroup.centralizer (L : Set G)).map
          (MulAut.conj (l * g)).toMonoidHom := by
        rw [← hsq]
        exact Subgroup.pow_mem _ hmem 2
      have hYeq : Y = (Subgroup.centralizer (L : Set G)).map
          (MulAut.conj (l * g)).toMonoidHom := h.z4_TI_conj hE1 hs hX haY hamem ha1
      rw [hYeq]
      exact hmem
    have hκY : ⁅y, l⁆ ∈ Y := by
      have h1 : (⁅y, l⁆)⁻¹ ∈ Y := by
        have e : (⁅y, l⁆)⁻¹ = (l * y * l⁻¹) * y⁻¹ := by
          rw [hlyl]
          group
        rw [e]
        exact Y.mul_mem hlY (Y.inv_mem hyY)
      simpa using Y.inv_mem h1
    exact hYV _ hκY hκV
  have hyL : ∀ l ∈ L, ⁅y, l⁆ = 1 := by
    intro l hl
    refine comm_eq_one_of_perfect hBlock.perfect (hMN hyM) (fun l' hl' => ?_) l hl
    rcases (key l' hl').2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact Subgroup.mem_centralizer_iff.2 fun l'' hl'' => by
        have := (key l'' hl'').1
        calc l'' * a = (l'' * a * l''⁻¹) * l'' := by group
          _ = a * l'' := by rw [this]
  have hyX : y ∈ Subgroup.centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have := hyL l hl
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hYX : Y ≤ Subgroup.centralizer (L : Set G) := by
    intro w hw
    rw [hYdef, mem_map_conj_iff, hX] at hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
    have e : w = y ^ k := by
      rw [hydef, conj_zpow, hk]
      group
    rw [e]
    exact Subgroup.zpow_mem _ hyX k
  have hcard : Nat.card ↥(Subgroup.centralizer (L : Set G)) ≤ Nat.card ↥Y := by
    rw [hYdef]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.centralizer (L : Set G))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv).le
  exact hgX (Subgroup.eq_of_le_of_card_ge hYX hcard)

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
