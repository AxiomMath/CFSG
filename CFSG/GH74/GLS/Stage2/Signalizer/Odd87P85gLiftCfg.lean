module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gSyl
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped commutatorElement

theorem card_map_of_inj_on {A B : Type} [Group A] [Group B] (f : A →* B) (P : Subgroup A)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, f x = f y → x = y) : Nat.card (P.map f) = Nat.card P := by
  have hinj' : Function.Injective (f.comp P.subtype) := fun x y hxy =>
    Subtype.ext (hinj x x.2 y y.2 hxy)
  have h : (f.comp P.subtype).range = P.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm

theorem lift_sylCfg {A : Type} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card N)) {α : A ⧸ N → A ⧸ N} {Pb Eb Fb : Subgroup (A ⧸ N)}
    (h : SylCfg α Pb Eb Fb) :
    ∃ P E F : Subgroup A, SylCfg id P E F ∧ IsPGroup 2 P ∧ P.map (QuotientGroup.mk' N) = Pb ∧
      E.map (QuotientGroup.mk' N) = Eb ∧ F.map (QuotientGroup.mk' N) = Fb ∧
      ∀ x ∈ P, ∀ y ∈ P, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
  classical
  have hPb2 : IsPGroup 2 Pb := IsPGroup.of_card (n := 6) (by rw [h.card_P]; norm_num)
  obtain ⟨P, hP2, hPmap, hinj, hnorm⟩ := lift_two_subgroup N hN Pb hPb2
  set mk := QuotientGroup.mk' N with hmk
  let E : Subgroup A := P ⊓ Eb.comap mk
  let F : Subgroup A := P ⊓ Fb.comap mk
  have hmemE : ∀ x, x ∈ E ↔ x ∈ P ∧ mk x ∈ Eb := fun x => Iff.rfl
  have hmemF : ∀ x, x ∈ F ↔ x ∈ P ∧ mk x ∈ Fb := fun x => Iff.rfl
  have hEmap : E.map mk = Eb := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hmemE x).mp hx).2
    · intro hy
      have : y ∈ P.map mk := hPmap ▸ h.E_le hy
      obtain ⟨x, hxP, rfl⟩ := this
      exact ⟨x, (hmemE x).mpr ⟨hxP, hy⟩, rfl⟩
  have hFmap : F.map mk = Fb := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hmemF x).mp hx).2
    · intro hy
      have : y ∈ P.map mk := hPmap ▸ h.F_le hy
      obtain ⟨x, hxP, rfl⟩ := this
      exact ⟨x, (hmemF x).mpr ⟨hxP, hy⟩, rfl⟩
  have hmemPb : ∀ x ∈ P, mk x ∈ Pb := fun x hx => hPmap ▸ ⟨x, hx, rfl⟩
  have hEP : ∀ e ∈ E, e ∈ P := fun e he => ((hmemE e).mp he).1
  have hFP : ∀ f ∈ F, f ∈ P := fun f hf => ((hmemF f).mp hf).1
  have hinjE : ∀ x ∈ E, ∀ y ∈ E, mk x = mk y → x = y := fun x hx y hy => hinj x (hEP x hx) y (hEP y hy)
  have hinjF : ∀ x ∈ F, ∀ y ∈ F, mk x = mk y → x = y := fun x hx y hy => hinj x (hFP x hx) y (hFP y hy)
  refine ⟨P, E, F, ?_, hP2, hPmap, hEmap, hFmap, hinj⟩
  exact
    { card_P := by rw [← card_map_of_inj_on mk P hinj, hPmap]; exact h.card_P
      exp_P := fun x hx => by
        apply hinj _ (P.pow_mem hx 4) 1 P.one_mem
        rw [map_pow, map_one]
        exact h.exp_P _ (hmemPb x hx)
      alpha_P := fun x hx => hx
      E_le := fun e he => hEP e he
      F_le := fun f hf => hFP f hf
      E_le_F := fun e he => (hmemF e).mpr ⟨hEP e he, h.E_le_F ((hmemE e).mp he).2⟩
      card_E := by rw [← card_map_of_inj_on mk E hinjE, hEmap]; exact h.card_E
      card_F := by rw [← card_map_of_inj_on mk F hinjF, hFmap]; exact h.card_F
      E_sq := fun e he => by
        apply hinj _ (P.mul_mem (hEP e he) (hEP e he)) 1 P.one_mem
        rw [map_mul, map_one]
        exact h.E_sq _ ((hmemE e).mp he).2
      E_cen := fun e he x hx => by
        apply hinj _ (P.mul_mem (hEP e he) hx) _ (P.mul_mem hx (hEP e he))
        rw [map_mul, map_mul]
        exact h.E_cen _ ((hmemE e).mp he).2 _ (hmemPb x hx)
      E_center := fun x hx hc => by
        refine (hmemE x).mpr ⟨hx, h.E_center _ (hmemPb x hx) (fun y hy => ?_)⟩
        have hy' : y ∈ P.map mk := hPmap ▸ hy
        obtain ⟨y₀, hy₀, rfl⟩ := hy'
        rw [← map_mul, ← map_mul, hc y₀ hy₀]
      E_alpha := fun e he => rfl
      E_comm := fun e he => by
        obtain ⟨a', ha', b', hb', hab'⟩ := h.E_comm _ ((hmemE e).mp he).2
        have ha'' : a' ∈ P.map mk := hPmap ▸ ha'
        have hb'' : b' ∈ P.map mk := hPmap ▸ hb'
        obtain ⟨a, haP, rfl⟩ := ha''
        obtain ⟨b, hbP, rfl⟩ := hb''
        refine ⟨a, haP, b, hbP, ?_⟩
        apply hinj _ (P.mul_mem (P.mul_mem (P.mul_mem haP hbP) (P.inv_mem haP)) (P.inv_mem hbP))
          e (hEP e he)
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        exact hab'
      F_comm := fun f hf g hg => by
        apply hinj _ (P.mul_mem (hFP f hf) (hFP g hg)) _ (P.mul_mem (hFP g hg) (hFP f hf))
        rw [map_mul, map_mul]
        exact h.F_comm _ ((hmemF f).mp hf).2 _ ((hmemF g).mp hg).2
      F_sq := fun f hf => by
        apply hinj _ (P.mul_mem (hFP f hf) (hFP f hf)) 1 P.one_mem
        rw [map_mul, map_one]
        exact h.F_sq _ ((hmemF f).mp hf).2
      fusion := fun e he hne e' he' hne' => by
        have hne₀ : mk e ≠ 1 := fun h1 => hne (hinj e (hEP e he) 1 P.one_mem (by rw [h1, map_one]))
        have hne₀' : mk e' ≠ 1 := fun h1 => hne' (hinj e' (hEP e' he') 1 P.one_mem (by rw [h1, map_one]))
        obtain ⟨nb, hnb, hnbe⟩ := h.fusion _ ((hmemE e).mp he).2 hne₀ _ ((hmemE e').mp he').2 hne₀'
        obtain ⟨n, hn, hmn⟩ := hnorm nb hnb
        refine ⟨n, hn, ?_⟩
        have hnP : n * e * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn e).mp (hEP e he)
        apply hinj _ hnP e' (hEP e' he')
        rw [map_mul, map_mul, map_inv, hmn]
        exact hnbe }

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
