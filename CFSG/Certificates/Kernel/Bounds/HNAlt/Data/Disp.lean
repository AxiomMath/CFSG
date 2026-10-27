module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel

public section

namespace CFSG.KD.HNA

@[expose] noncomputable def Ed (D : Nat) : Nat → Nat :=
  List.getD [fun _ => 0, E1, E2, E3, E4, E5, E6, fun _ => 0, E8, E9, E10, E11, E12, E13, E14, E15,
    E16, E17, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27, E28, E29, E30, E31, E32, E33, E34,
    E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53,
    E54, E55, E56, E57, E58, E59, E60, E61, E62, E63, E64, E65, E66, E67, E68, E69, E70, E71, E72,
    E73, E74, E75, E76, E77, E78, E79, E80, E81] D (fun _ => 0)

@[expose] noncomputable def SGd (D : Nat) : Nat :=
  List.getD [0, SG1, SG2, SG3, SG4, SG5, SG6, 0, SG8, SG9, SG10, SG11, SG12, SG13, SG14, SG15, SG16,
    SG17, SG18, SG19, SG20, SG21, SG22, SG23, SG24, SG25, SG26, SG27, SG28, SG29, SG30, SG31, SG32,
    SG33, SG34, SG35, SG36, SG37, SG38, SG39, SG40, SG41, SG42, SG43, SG44, SG45, SG46, SG47, SG48,
    SG49, SG50, SG51, SG52, SG53, SG54, SG55, SG56, SG57, SG58, SG59, SG60, SG61, SG62, SG63, SG64,
    SG65, SG66, SG67, SG68, SG69, SG70, SG71, SG72, SG73, SG74, SG75, SG76, SG77, SG78, SG79, SG80,
    SG81] D 0

end CFSG.KD.HNA

end
