module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockBase
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockInd
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockPure
import CFSG.LocalAnalysis.GLTheoremB.I2810.BlocksChief
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Hom

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]
variable {e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7))}
  {V₄ B : Subgroup ↥(alternatingGroup (Fin 7))} {Ik : Subgroup X}

theorem inv_mul_mem_W (h : Setup28 W K S) (d : A5Data W K S e V₄ B Ik) {k x : ↥K}
    (hk : (k : X) ∈ Ik) (hx : (x : X) ∈ S) (hπ : piOf e k = piOf e x) :
    (k : X)⁻¹ * (x : X) ∈ W := by
  obtain ⟨m, hm⟩ := A5Base.exists_two_pow_of_mem h hx
  have hzc : toBar W K (k⁻¹ * x) ∈ Subgroup.center ↥(bar W K) := by
    rw [← A5Base.piBar_eq_one_iff e]
    show piOf e (k⁻¹ * x) = 1
    rw [map_mul, map_inv, hπ, inv_mul_cancel]
  have hxm : toBar W K x ^ (2 ^ m) = 1 := A5Base.toBar_pow_two_pow hm
  have hcomm : Commute (toBar W K k) (toBar W K (k⁻¹ * x)) :=
    Subgroup.mem_center_iff.1 hzc (toBar W K k)
  have hx' : toBar W K x = toBar W K k * toBar W K (k⁻¹ * x) := by
    rw [← map_mul]
    congr 1
    group
  have h1 : (toBar W K k) ^ (2 ^ m) * (toBar W K (k⁻¹ * x)) ^ (2 ^ m) = 1 := by
    rw [← hcomm.mul_pow, ← hx']
    exact hxm
  have hk₂ : (((k ^ (2 ^ m))⁻¹ : ↥K) : X) ∈ Ik := by
    have : (((k ^ (2 ^ m))⁻¹ : ↥K) : X) = ((k : X) ^ (2 ^ m))⁻¹ := by simp
    rw [this]
    exact Ik.inv_mem (Ik.pow_mem hk _)
  have h2 : toBar W K ((k ^ (2 ^ m))⁻¹) = (toBar W K (k⁻¹ * x)) ^ (2 ^ m) := by
    rw [map_inv, map_pow]
    exact inv_eq_of_mul_eq_one_right h1
  have h3 : piOf e ((k ^ (2 ^ m))⁻¹) = 1 := by
    show A5Base.piBar e (toBar W K _) = 1
    rw [h2]
    exact (A5Base.piBar_eq_one_iff e _).2 (Subgroup.pow_mem _ hzc _)
  have h4 := d.Ik_ker _ hk₂ h3
  have h5 : toBar W K ((k ^ (2 ^ m))⁻¹) = 1 := (BlocksChief.toBar_eq_one_iff _).2 h4
  rw [h2] at h5
  have h6 : toBar W K (k⁻¹ * x) = 1 := A5Base.central_eq_one_of_two_pow h hzc h5
  have h7 := (BlocksChief.toBar_eq_one_iff _).1 h6
  simpa using h7

theorem a5_I_eq_aux (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    Ik ⊔ S = Ik ⊔ kerAct W K S := by
  apply le_antisymm
  · refine sup_le le_sup_left fun s hs => ?_
    obtain ⟨x, hxS, hsx, hxV⟩ := d.sv.dec s hs
    obtain ⟨k, hkIk, hkx⟩ := d.Ik_onto _ (d.VB hxV)
    have hz : (k : X)⁻¹ * (x : X) ∈ W := inv_mul_mem_W h d hkIk hxS hkx
    have hxe : (x : X) = (k : X) * ((k : X)⁻¹ * (x : X)) := by group
    have hx : (x : X) ∈ Ik ⊔ kerAct W K S := by
      rw [hxe]
      exact (Ik ⊔ kerAct W K S).mul_mem (Subgroup.mem_sup_left hkIk) (Subgroup.mem_sup_right (hR.w1_le hz))
    have hse : s = (s * (x : X)⁻¹) * (x : X) := by group
    rw [hse]
    exact (Ik ⊔ kerAct W K S).mul_mem (Subgroup.mem_sup_right hsx) hx
  · exact sup_le_sup_left hR.w1_S _

theorem a5_I_hom_aux (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    ∃ φ : ↥(Ik ⊔ S) →* ↥(alternatingGroup (Fin 5)), Function.Surjective φ ∧
      ∀ x : ↥(Ik ⊔ S), φ x = 1 ↔ (x : X) ∈ kerAct W K S := by
  obtain ⟨θ⟩ := d.Bquot
  have heq := a5_I_eq_aux h hR d
  have hIkN : Ik ≤ Subgroup.normalizer (kerAct W K S : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hR.w1_nrm k (Subgroup.mem_sup_left (d.Ik_le hk)) w hw, fun hw => ?_⟩
    have := hR.w1_nrm k⁻¹ (Subgroup.mem_sup_left (d.Ik_le (Ik.inv_mem hk))) _ hw
    simpa [mul_assoc] using this
  have hdec : ∀ x : ↥(Ik ⊔ S), ∃ p : X × ↥Ik, p.1 ∈ kerAct W K S ∧ (x : X) = p.1 * (p.2 : X) := by
    intro x
    have hx : (x : X) ∈ kerAct W K S ⊔ Ik := by
      rw [sup_comm, ← heq]
      exact x.2
    obtain ⟨w, hw, k, hk, hxe⟩ := CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer hIkN hx
    exact ⟨(w, ⟨k, hk⟩), hw, hxe⟩
  let ρ₀ : ↥Ik →* ↥K := Subgroup.inclusion d.Ik_le
  let Λ : ↥Ik →* ↥(alternatingGroup (Fin 5)) :=
    θ.toMonoidHom.comp (((piOf e).comp ρ₀).codRestrict B fun k => d.Ik_into (ρ₀ k) k.2)
  have hΛ : ∀ k : ↥Ik, ((θ.symm (Λ k) : ↥B) : ↥(alternatingGroup (Fin 7))) = piOf e (ρ₀ k) := by
    intro k
    simp [Λ]
  have hΛ1 : ∀ k : ↥Ik, Λ k = 1 ↔ piOf e (ρ₀ k) = 1 := by
    intro k
    simp only [Λ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have key : ∀ (k k' : ↥Ik) (w w' : X), w ∈ kerAct W K S → w' ∈ kerAct W K S →
      w * (k : X) = w' * (k' : X) → Λ k = Λ k' := by
    intro k k' w w' hw hw' hwk
    have hu : ((k * k'⁻¹ : ↥Ik) : X) ∈ kerAct W K S := by
      have : ((k * k'⁻¹ : ↥Ik) : X) = w⁻¹ * w' := by
        show (k : X) * (k' : X)⁻¹ = w⁻¹ * w'
        calc (k : X) * (k' : X)⁻¹ = w⁻¹ * (w * k) * (k' : X)⁻¹ := by group
          _ = w⁻¹ * (w' * k') * (k' : X)⁻¹ := by rw [hwk]
          _ = w⁻¹ * w' := by group
      rw [this]
      exact (kerAct W K S).mul_mem ((kerAct W K S).inv_mem hw) hw'
    have huK : ((k * k'⁻¹ : ↥Ik) : X) ∈ K ⊓ kerAct W K S := ⟨d.Ik_le (k * k'⁻¹).2, hu⟩
    rw [hR.k_w1] at huK
    have hπ : piOf e (ρ₀ (k * k'⁻¹)) = 1 := A5Base.piOf_eq_one_of_mem huK.2
    have h1 : Λ (k * k'⁻¹) = 1 := (hΛ1 _).2 hπ
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  let f : ↥(Ik ⊔ S) → ↥(alternatingGroup (Fin 5)) := fun x => Λ (Classical.choose (hdec x)).2
  have hf : ∀ (x : ↥(Ik ⊔ S)) (w : X) (k : ↥Ik), w ∈ kerAct W K S → (x : X) = w * (k : X) →
      f x = Λ k := by
    intro x w k hw hx
    obtain ⟨hw0, hx0⟩ := Classical.choose_spec (hdec x)
    exact key _ _ _ _ hw0 hw (hx0.symm.trans hx)
  have hmul : ∀ x y : ↥(Ik ⊔ S), f (x * y) = f x * f y := by
    intro x y
    obtain ⟨⟨w, k⟩, hw, hx⟩ := hdec x
    obtain ⟨⟨w', k'⟩, hw', hy⟩ := hdec y
    have hxy : ((x * y : ↥(Ik ⊔ S)) : X) =
        (w * ((k : X) * w' * (k : X)⁻¹)) * ((k * k' : ↥Ik) : X) := by
      show (x : X) * (y : X) = _
      rw [hx, hy]
      show _ = _ * ((k : X) * (k' : X))
      group
    have hw'' : w * ((k : X) * w' * (k : X)⁻¹) ∈ kerAct W K S :=
      (kerAct W K S).mul_mem hw (hR.w1_nrm k (Subgroup.mem_sup_left (d.Ik_le k.2)) w' hw')
    rw [hf (x * y) _ (k * k') hw'' hxy, hf x w k hw hx, hf y w' k' hw' hy, map_mul]
  refine ⟨MonoidHom.mk' f hmul, ?_, ?_⟩
  · intro a
    have hb : ((θ.symm a : ↥B) : ↥(alternatingGroup (Fin 7))) ∈ B := (θ.symm a).2
    obtain ⟨k, hkIk, hk⟩ := d.Ik_onto _ hb
    let kI : ↥Ik := ⟨k, hkIk⟩
    let x : ↥(Ik ⊔ S) := ⟨k, Subgroup.mem_sup_left hkIk⟩
    refine ⟨x, ?_⟩
    show f x = a
    rw [hf x 1 kI (kerAct W K S).one_mem (by simp [x, kI])]
    apply θ.symm.injective
    apply Subtype.ext
    rw [hΛ]
    exact hk
  · intro x
    obtain ⟨⟨w, k⟩, hw, hx⟩ := hdec x
    show f x = 1 ↔ _
    rw [hf x w k hw hx]
    constructor
    · intro h1
      have h2 : piOf e (ρ₀ k) = 1 := (hΛ1 k).1 h1
      have h3 := d.Ik_ker (ρ₀ k) k.2 h2
      rw [hx]
      exact (kerAct W K S).mul_mem hw (hR.w1_le h3)
    · intro hx1
      have hk1 : (k : X) ∈ kerAct W K S := by
        have : (k : X) = w⁻¹ * (x : X) := by rw [hx]; group
        rw [this]
        exact (kerAct W K S).mul_mem ((kerAct W K S).inv_mem hw) hx1
      have hkK : (k : X) ∈ K ⊓ kerAct W K S := ⟨d.Ik_le k.2, hk1⟩
      rw [hR.k_w1] at hkK
      exact (hΛ1 k).2 (A5Base.piOf_eq_one_of_mem hkK.2)

theorem a5_I_sylow_aux (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (Ik ⊔ S) := by
  obtain ⟨φ, hφ, hker⟩ := a5_I_hom_aux h hR d
  refine ⟨le_sup_right, h.hS, ?_⟩
  have h1 : (kerAct W K S).relIndex (Ik ⊔ S) = 60 := by
    show ((kerAct W K S).subgroupOf (Ik ⊔ S)).index = 60
    have : (kerAct W K S).subgroupOf (Ik ⊔ S) = φ.ker := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hker]
    rw [this, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top, A5Pure.card_alt5]
  have h2 : (kerAct W K S).relIndex S = 4 := d.sv.idx
  have h3 := Subgroup.relIndex_mul_relIndex (kerAct W K S) S (Ik ⊔ S) hR.w1_S le_sup_right
  rw [h1, h2] at h3
  have h4 : S.relIndex (Ik ⊔ S) = 15 := by omega
  show ¬ 2 ∣ S.relIndex (Ik ⊔ S)
  rw [h4]
  decide

theorem a5_I_dec_zker_aux (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    (∀ i ∈ Ik ⊔ S, ∃ k ∈ K, k ∈ Ik ⊔ S ∧ i * k⁻¹ ∈ kerAct W K S) ∧
      (Ik ⊔ S) ⊓ zPre W K ≤ kerAct W K S := by
  have heq := a5_I_eq_aux h hR d
  have hIkN : Ik ≤ Subgroup.normalizer (kerAct W K S : Set X) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hR.w1_nrm k (Subgroup.mem_sup_left (d.Ik_le hk)) w hw, fun hw => ?_⟩
    have := hR.w1_nrm k⁻¹ (Subgroup.mem_sup_left (d.Ik_le (Ik.inv_mem hk))) _ hw
    simpa [mul_assoc] using this
  have hdec : ∀ i ∈ Ik ⊔ S, ∃ n ∈ kerAct W K S, ∃ k ∈ Ik, i = n * k := by
    intro i hi
    have hi' : i ∈ kerAct W K S ⊔ Ik := by
      rw [sup_comm, ← heq]
      exact hi
    exact CFSG.Quasithin.F53Push.mem_sup_of_le_normalizer hIkN hi'
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨n, hn, k, hk, rfl⟩ := hdec i hi
    refine ⟨k, d.Ik_le hk, Subgroup.mem_sup_left hk, ?_⟩
    simpa using hn
  · obtain ⟨n, hn, k, hk, hik⟩ := hdec i hi.1
    have hiK : i ∈ K := hi.2.1
    have hnK : n ∈ K := by
      have : n = i * (k : X)⁻¹ := by rw [hik]; group
      rw [this]
      exact K.mul_mem hiK (K.inv_mem (d.Ik_le hk))
    have hnW : n ∈ W := by
      have : n ∈ K ⊓ kerAct W K S := ⟨hnK, hn⟩
      rw [hR.k_w1] at this
      exact this.2
    have hkz : k ∈ zPre W K := by
      have : k = n⁻¹ * i := by rw [hik]; group
      rw [this]
      exact (zPre W K).mul_mem ((zPre W K).inv_mem (A5Base.inf_le_zPre ⟨hnK, hnW⟩)) hi.2
    have hkW : k ∈ W :=
      d.Ik_ker ⟨k, d.Ik_le hk⟩ hk ((A5Base.piOf_eq_one_iff e ⟨k, d.Ik_le hk⟩).2 hkz)
    rw [hik]
    exact (kerAct W K S).mul_mem hn (hR.w1_le hkW)

theorem a5_I_gen_aux (h : Setup28 W K S) (hR : Red28 W K S) (d : A5Data W K S e V₄ B Ik) :
    ∀ H : Subgroup X, H ≤ K → (Ik ⊔ S) ⊓ K ≤ H →
      (∀ k ∈ K, k ∈ Subgroup.normalizer (S : Set X) → k ∈ H) →
        K ≤ H ⊔ (K ⊓ kerAct W K S) := by
  intro H hHK hIK hN
  let Hk : Subgroup ↥K := H.subgroupOf K
  let P : Subgroup ↥(alternatingGroup (Fin 7)) := Hk.map (piOf e)
  have hB : B ≤ P := fun b hb => by
    obtain ⟨k, hkIk, hk⟩ := d.Ik_onto b hb
    exact ⟨k, hIK ⟨Subgroup.mem_sup_left hkIk, d.Ik_le hkIk⟩, hk⟩
  have hNV : Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) ≤ P := fun g hg => by
    obtain ⟨k, hkN, hk⟩ := d.NK g hg
    exact ⟨k, hN k k.2 hkN, hk⟩
  have hPtop : P = ⊤ := d.Bgen P hB hNV
  let Hb : Subgroup ↥(bar W K) := Hk.map (toBar W K)
  have hHb : Hb = ⊤ := by
    refine A5Base.eq_top_of_sup_center (A5Base.perfect_bar h) Hb fun g => ?_
    obtain ⟨k, rfl⟩ := BlocksChief.toBar_surjective W K g
    have hk : piOf e k ∈ P := hPtop ▸ Subgroup.mem_top _
    obtain ⟨h', hh', hk'⟩ := hk
    have hz : ((h'⁻¹ * k : ↥K) : X) ∈ zPre W K := by
      rw [← A5Base.piOf_eq_one_iff e, map_mul, map_inv, hk', inv_mul_cancel]
    refine ⟨toBar W K h', Subgroup.mem_map_of_mem _ hh', toBar W K (h'⁻¹ * k),
      BlocksChief.center_of_zPre hz, ?_⟩
    rw [← map_mul]
    congr 1
    group
  intro k hk
  have hkb : toBar W K ⟨k, hk⟩ ∈ Hb := hHb ▸ Subgroup.mem_top _
  obtain ⟨h', hh', hbh⟩ := hkb
  have hW : (h' : X)⁻¹ * k ∈ W := A5Ind.toBar_eq_iff.1 hbh
  have hk' : k = (h' : X) * ((h' : X)⁻¹ * k) := by group
  rw [hk']
  exact (H ⊔ (K ⊓ kerAct W K S)).mul_mem (Subgroup.mem_sup_left hh')
    (Subgroup.mem_sup_right ⟨K.mul_mem (K.inv_mem h'.2) hk, hR.w1_le hW⟩)

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Hom
